-- Prove2me | Theorems.Thm_MinFracProphet_lemma_2
-- name    : MinFracProphet.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:34:46.302525+00:00
-- url     : https://prove2.me/theorems/00b095ac-2b62-4a00-93b3-196acda1ff11
-- title:
--   Lemma 2: under a mean constraint, $\mathbb E[f(C)]$ with $f$ strictly concave is minimized only by the long-shot law on $\{\ell,u\}$
-- statement:
--   Let $0<\ell\le\mu\le u<\infty$, let $\mathcal C$ be the set of probability distributions on $\mathbb R$ carried by $[\ell,u]$ with mean $\mu$, and let $f$ be strictly concave on $[\ell,u]$. Consider
--   $$
--   \min_{C\in\mathcal C}\ \mathbb E[f(C)].
--   $$
--   1. Every minimizer is concentrated on $\{\ell,u\}$; if $\ell<u$, it is the long-shot law $D^\star$ with
--   $$
--   \mathbb P[C=u]=p_u=\frac{\mu-\ell}{u-\ell},\qquad \mathbb P[C=\ell]=p_\ell=\frac{u-\mu}{u-\ell}.
--   $$
--   2. If $\ell<u$, then $D^\star\in\mathcal C$ and $D^\star$ is a minimizer.
--
--   The upper-bound proof of Theorem 2 applies this lemma one seller at a time to find the distributions that are worst for the non-adaptive algorithm.
--
--   **Formalization Note** Distributions are probability measures $\nu$ on $\mathbb R$ with $\nu([\ell,u]^c)=0$, and $\mathbb E[f(C)]=\int f\,d\nu$ is a Bochner integral. It is never the junk value: a function concave on $[\ell,u]$ is bounded and Borel there.
--
--   Differences from the source:
--   - reading: a solution of (9), if it exists, is C = u w.p. p_u, ℓ w.p. p_ℓ → every minimizer is concentrated on {ℓ,u}, and equals the law with masses p_u, p_ℓ when ℓ < u; reason: at ℓ = u the printed probabilities are 0/0 and 𝒞 = {δ_ℓ}; the support clause covers that case
--   - generalization: (no existence claim) → for ℓ < u the long-shot law belongs to 𝒞 and is a minimizer; reason: an added conclusion; the first clause is the page’s statement, and §3 uses the minimizer
--   - generalization: f a strictly concave function → f : ℝ → ℝ strictly concave on [ℓ,u] only; reason: every strictly concave function whose domain contains [ℓ,u] satisfies the hypothesis, so the page’s lemma is a special case
--   - encoding: random variables C whose distribution is supported on [ℓ,u] with E[C] = µ; E[f(C)] → probability measures ν on ℝ with ν([ℓ,u]ᶜ) = 0 and ∫ c dν = µ; ∫ f dν (Bochner); reason: the problem depends only on the law of C
-- source:
--   Qin, Vardi, Wierman, Minimization Fractional Prophet Inequalities for Sequential Procurement, author manuscript (INFORMS template, sha256 672fa87c…79125d3), Lemma 2, p.12 (restated p.20)

import Mathlib

open MeasureTheory

namespace MinFracProphet

/-- **Lemma 2**, p.12 of J. Qin, S. Vardi, A. Wierman, *Minimization Fractional Prophet
Inequalities for Sequential Procurement*, author manuscript (sha256 672fa87c…79125d3).

Let `0 < ℓ ≤ μ ≤ u < ∞`, let `𝒞` be the set of probability laws on `ℝ` carried by `[ℓ,u]` with
mean `μ`, and let `f` be strictly concave on `[ℓ,u]`. Then:

1. every minimizer `ν⋆ ∈ 𝒞` of `ν ↦ E_ν[f(C)] = ∫ f dν` over `𝒞` is concentrated on `{ℓ, u}`, and
   if `ℓ < u` it is the long-shot law `D⋆` that puts mass `p_u = (μ-ℓ)/(u-ℓ)` on `u` and
   `p_ℓ = (u-μ)/(u-ℓ)` on `ℓ`;
2. (existence) if `ℓ < u`, then `D⋆ ∈ 𝒞` and `D⋆` minimizes `∫ f dν` over `𝒞`.

**Formalization Note** The page states "a solution of (9), if it exists, is C = …" (R7): clause 1
is that statement; at `ℓ = u` the printed probabilities are `0/0`, and `𝒞 = {δ_ℓ}`, so the
probabilities are stated for `ℓ < u` only. Clause 2 (existence) is an addition, the fact §3 uses.
"Strictly concave" is read on `[ℓ,u]`, where the laws live. The integrals are Bochner integrals;
they are genuine (not the junk value `0`): a function concave on `[ℓ,u]` is bounded and Borel on
`[ℓ,u]`, which carries every law of `𝒞`. -/
theorem lemma_2 (ℓ μ u : ℝ) (hℓ : 0 < ℓ) (hℓμ : ℓ ≤ μ) (hμu : μ ≤ u)
    (f : ℝ → ℝ) (hf : StrictConcaveOn ℝ (Set.Icc ℓ u) f) :
    let 𝒞 : Set (Measure ℝ) :=
      {ν | IsProbabilityMeasure ν ∧ ν (Set.Icc ℓ u)ᶜ = 0 ∧ ∫ c, c ∂ν = μ}
    let Dstar : Measure ℝ :=
      ENNReal.ofReal ((u - μ) / (u - ℓ)) • Measure.dirac ℓ +
        ENNReal.ofReal ((μ - ℓ) / (u - ℓ)) • Measure.dirac u
    (∀ νstar ∈ 𝒞, (∀ ν ∈ 𝒞, ∫ c, f c ∂νstar ≤ ∫ c, f c ∂ν) →
        νstar ({ℓ, u} : Set ℝ)ᶜ = 0 ∧ (ℓ < u → νstar = Dstar)) ∧
      (ℓ < u → Dstar ∈ 𝒞 ∧ ∀ ν ∈ 𝒞, ∫ c, f c ∂Dstar ≤ ∫ c, f c ∂ν) := by sorry

end MinFracProphet
