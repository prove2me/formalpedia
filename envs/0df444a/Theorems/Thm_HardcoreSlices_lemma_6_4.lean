-- Prove2me | Theorems.Thm_HardcoreSlices_lemma_6_4
-- name    : HardcoreSlices.lemma_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:37:55.140828+00:00
-- url     : https://prove2.me/theorems/d6df1c22-1400-4384-a48b-8aad3894155f
-- title:
--   Lemma 6.4 — approximate counting from pin-in samplers
-- statement:
--   Let $X$ be a pure $k$-dimensional complex on $[n]$ with a weight $w>0$ on $X(k)$, and let $Z_\tau=\sum_{S\in X(k),\,\tau\subseteq S}w(S)$. Let `samp` be a sampler such that, for every face $\tau$ and every $\eta\in(0,1)$, the law `samp τ η` is supported on the facets containing $\tau$ and is within total variation $\eta$ of $\mu_{|\tau}$. Then for every face $\tau$ and all $\varepsilon,\delta\in(0,1)$, the pin-in estimator with $\ell=k-|\tau|$, $h=\varepsilon/(8\ell n)$ and $M=\lceil2\log(2\ell n/\delta)/h^2\rceil$ satisfies
--   $$\Pr\bigl[(1-\varepsilon)Z_\tau\le\hat Z_\tau\le(1+\varepsilon)Z_\tau\bigr]\ge1-\delta.$$
--   It makes exactly $\ell M$ sampler calls, each at accuracy $h/2$, and
--   $$\ell M\le n\Bigl(2\log\frac{2n^2}\delta\cdot\bigl(\frac{8n^2}\varepsilon\bigr)^2+1\Bigr),$$
--   so an FPAUS for every $\mu_{|\tau}$ yields an FPRAS for $Z_\tau$.
--
--   Differences from the source:
--   - reading: if µ|τ has an FPAUS then Zτ has an FPRAS → the explicit estimator of p.29 over an arbitrary sampler, with guarantee, exact call count and polynomial bound; reason: a bare existence is empty for a Lean function able to read w; the theorem is what the proof gives
--   - encoding: polynomial-time computable w → w is a function, read only at the final facet, once; reason: the estimator makes one evaluation, so polynomial time is immediate from the hypothesis of the source
--   - encoding: argmax → ties to the smallest vertex of [n]; reason: the proof works for any maximizer
-- source:
--   Kocurek, Oveis Gharan, Tjowasi, Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold, arXiv:2604.21847 (version held, sha256 363c225d…), Lemma 6.4, p.28, with its proof, p.29

import Mathlib
import Definitions.Def_SteurerHDX_IsPure
import Definitions.Def_SteurerHDX_faces
import Definitions.Def_mm_mixing
import Definitions.Def_HardcoreSlices_downUp
import Definitions.Def_HardcoreSlices_pinInRun

open Classical

namespace HardcoreSlices

/-- **Lemma 6.4 (Approximate counting from strictly pin-in samplers).** Kocurek, Oveis Gharan, Tjowasi, *Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold*, arXiv:2604.21847 (version held, sha256 363c225d…), p.28: "Let `X` be `k`-dimensional simplicial complex over `[n]` with a polynomial-time computable weight function `w : X(k) → R+`.
For any `τ ∈ X`, define `Zτ = Σ_{S∈X, τ⊆S} w(S)`. Let `µ(S) = w(S)/Σ_{S∈X(k)} w(S)` define `µ` on `X(k)`. Then if `µ|τ` has an FPAUS for any `τ ∈ X` then `Zτ` has an FPRAS."
The estimator (p.29): `ℓ = k − |τ|`, `h = ε/(8ℓn)`, `m = ⌈2 log(2ℓn/δ) / h²⌉` samples within total variation `h/2` of `µ|τ` at each of `ℓ` iterations, pin in a vertex of maximum empirical frequency,
and return `Ẑτ := w(S) / Π_{r=1}^{ℓ} p̂r`.

**Formalization Note.** A bare "there is an FPRAS" is empty for a Lean function that can read `w`, so this is the explicit estimator `pinInRun` over an arbitrary sampler `samp` (the "promised FPAUS"), which is the
only access to the complex besides `X`'s link vertices and `w` at the final facet. `samp τ η` is supported on the facets containing `τ` ("Outputs `x`", `x ∈ Ω`, Definition 2.13) and is within total variation `η` of `µ|τ`,
which is carried by those facets. The conclusion has three parts: the guarantee; the number of sampler calls, exactly `ℓm`, each with accuracy `h/2` by construction; and an explicit `poly(n, 1/ε, log 1/δ)` bound on that number. -/
theorem lemma_6_4 {n k : ℕ} (X : Finset (Finset (Fin n))) (hX : SteurerHDX.IsPure X k)
    (w : Finset (Fin n) → ℝ) (hw : ∀ S ∈ SteurerHDX.faces X k, 0 < w S)
    (samp : Finset (Fin n) → ℝ → PMF (Finset (Fin n)))
    (hsupp : ∀ τ ∈ X, ∀ η : ℝ, 0 < η → η < 1 → ∀ S, samp τ η S ≠ 0 → S ∈ SteurerHDX.faces X k ∧ τ ⊆ S)
    (htv : ∀ τ ∈ X, ∀ η : ℝ, 0 < η → η < 1 →
      MarkovMixing.tvDist (fun S => (samp τ η S).toReal) (condLaw (SteurerHDX.faces X k) w τ) ≤ η)
    (τ : Finset (Fin n)) (hτ : τ ∈ X) (ε δ : ℝ) (hε : 0 < ε) (hε' : ε < 1) (hδ : 0 < δ) (hδ' : δ < 1) :
    ENNReal.ofReal (1 - δ) ≤
        (pinInRun X samp (pinH n (k - τ.card) ε / 2) (pinM n (k - τ.card) ε δ) τ (k - τ.card)).toOuterMeasure
          {st | (1 - ε) * facetMass (SteurerHDX.faces X k) w τ ≤ w st.pinned / st.prod ∧
            w st.pinned / st.prod ≤ (1 + ε) * facetMass (SteurerHDX.faces X k) w τ} ∧
      (∀ st ∈ (pinInRun X samp (pinH n (k - τ.card) ε / 2) (pinM n (k - τ.card) ε δ) τ (k - τ.card)).support,
        st.calls = (k - τ.card) * pinM n (k - τ.card) ε δ) ∧
      (((k - τ.card) * pinM n (k - τ.card) ε δ : ℕ) : ℝ) ≤
        (n : ℝ) * (2 * Real.log (2 * (n : ℝ) ^ 2 / δ) * (8 * (n : ℝ) ^ 2 / ε) ^ 2 + 1) := by sorry

end HardcoreSlices
