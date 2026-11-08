-- Prove2me | Theorems.Thm_HardcoreSlices_lemmas_6_1_6_2
-- name    : HardcoreSlices.lemmas_6_1_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:40:26.468199+00:00
-- url     : https://prove2.me/theorems/9431dee9-2752-4a82-84c7-bea3598ac9a7
-- title:
--   Lemmas 6.1, 6.2 and Corollaries 6.6, 6.7 — slice counters and pin-in samplers
-- statement:
--   Let $\gamma$ be a threshold at $\ell=6$. There is $c>0$ such that for all large $\Delta$ there are four programs of the published real RAM and a polynomial, depending only on $\Delta$, for which, with high probability over a random $\Delta$-regular bipartite graph $G$:
--
--   1. (Lemma 6.1) for $k_X,k_Y\le(1-\gamma)\alpha^*(\Delta)|X|$ and every face $\tau$ of the two-sided slice, the first program is an FPRAS for $|\mathcal I^{(\tau)}_{k_X,k_Y}(G)|$;
--   2. (Corollary 6.6) for the same data, the third program is an FPAUS for $\mu^{(k_X,k_Y)}_{|\tau}$;
--   3. (Lemma 6.2) for every $\lambda\in(0,c/\sqrt\Delta]$, each side, $k\in[(1-\gamma)\alpha^*|X|,4\lambda|X|]$ and every $\tau$ in that side, the second program is an FPRAS for $\sum_{S\in\binom Xk,\,\tau\subseteq S}\lambda^k(1+\lambda)^{|Y\setminus N(S)|}$;
--   4. (Corollary 6.7) for the same data with $|\tau|\le k$, the fourth program is an FPAUS for $(\mu_\lambda^{(k)})_{|\tau}$.
--
--   Every FPRAS runs within $K(|X|+1+1/\varepsilon+\log(1/\delta))^d$ steps and every FPAUS within $K(|X|+1+\log(1/\varepsilon))^d$. These are the subroutines of Theorem 1.4.
--
--   Differences from the source:
--   - reading: γ = o∆(1) "fixed globally" (p.19) → every sequence γ with IsThreshold 6 γ; reason: the regimes share one γ (p.4) and p.20 sets ℓ ≥ 6; separate existentials would lose the overlap
--   - generalization: the sentence fixes no order between λ and the high-probability event → λ quantified inside the event, uniformly over its range; reason: the events the proof uses do not mention λ; a fixed-λ statement follows by specialization
--   - reading: polynomial time, no model named → worst-case steps of the published unit-cost real RAM, fair coins, rational literals, no bit size of λ; reason: λ is a real input and Definitions 2.12, 2.13 bound the time in n, ε, δ only; the algorithm is arithmetic
--   - reading: Ẑ ∈ R+ → 0 ≤ z on every tape; reason: on the accepted tapes z ≥ (1−ε)Z anyway, so this concerns only failing tapes
--   - encoding: FPAUS for µ|τ on the facets σ \ τ of the link → output is the full facet σ ⊇ τ; reason: a bijection, and the sampler of p.30 reads marginals from it
--   - encoding: four statements with high probability → one conjunction under one event, four programs chosen first; reason: the intersection of four high-probability events is one, and the proof of Theorem 1.4 uses it so
--   - reading: no bound on λ in the four sentences → 0 < λ ≤ c/√Δ with c > 0 chosen first, in the one-sided clauses; reason: §6 works at fugacity λ ≲ 1/√∆ (p.26), and the range k ≤ 4λ|X| is that of Theorem 1.9, which needs it
-- source:
--   Kocurek, Oveis Gharan, Tjowasi, Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold, arXiv:2604.21847 (version held, sha256 363c225d…), Lemmas 6.1, 6.2, p.26; Corollaries 6.6, 6.7, pp.28–29

import Mathlib
import Definitions.Def_HardcoreSlices_IsThreshold
import Definitions.Def_HardcoreSlices_twoSidedSlice
import Definitions.Def_HardcoreSlices_oneSidedSlice
import Definitions.Def_HardcoreSlices_IsFPRASRun

open Classical

namespace HardcoreSlices

open ExpanderBIS.RandomHardCore

/-- **Lemmas 6.1, 6.2 and Corollaries 6.6, 6.7.** Kocurek, Oveis Gharan, Tjowasi, *Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold*, arXiv:2604.21847 (version held, sha256 363c225d…), pp.26, 28–29.

Lemma 6.1: an FPRAS for `|I^(τ)_{kX,kY}(G)|` with `I^(τ)_{kX,kY}(G) := Xτ(kX + kY − |τ|)`, when `kX, kY ≤ (1 − γ)α∗(∆)|X|`.
Lemma 6.2: an FPRAS for `Z^(X,k)_{G,τ} := Σ_{S∈(X choose k), τ⊆S} λ^k (1 + λ)^{|Y\N(S)|}`, for any `τ ⊆ X`, when `k ∈ [(1 − γ)α∗|X|, 4λ|X|]`.
Corollary 6.6: an FPAUS for `µ|τ^(kX,kY)`, for any `τ` in the two-sided slice, when `kX, kY ≤ (1 − γ)α∗(∆)|X|`.
Corollary 6.7: an FPAUS for `(µλ^(k))|τ`, for any `τ ⊆ X` with `|τ| ≤ k`, when `k ∈ [(1 − γ)α∗|X|, 4λ|X|]`.

**Formalization Note.** One high-probability event, as in the proof of Theorem 1.4. The four programs and the polynomial are chosen before `m`, `G`, `λ`, `kX`, `kY`, `k`, `τ`, `ε`, `δ`, and depend on `∆` only. Integer cells
`-1, -2` hold `kX, kY`, or the side and `k`; bitmap `0` holds `τ`; real memory holds `λ` (where used), `ε`, `δ` (where used). The law `µ|τ` is carried by the facets containing `τ`, so a sample is a full facet.
The programs find their own starting facet: the walk's start is not an input. -/
theorem lemmas_6_1_6_2 (γ : ℕ → ℝ) (hγ : IsThreshold 6 γ) :
    ∃ c : ℝ, 0 < c ∧ ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ →
      ∃ (P₁ P₂ P₃ P₄ : SubsetConvFPRAS.Program) (K d : ℕ),
        SubsetConvFPRAS.Admissible P₁ ∧ SubsetConvFPRAS.Admissible P₂ ∧
        SubsetConvFPRAS.Admissible P₃ ∧ SubsetConvFPRAS.Admissible P₄ ∧
        AlmostEvery Δ (fun m G =>
          (∀ kX kY : ℕ, (kX : ℝ) ≤ (1 - γ Δ) * alphaStar Δ * m → (kY : ℝ) ≤ (1 - γ Δ) * alphaStar Δ * m →
            ∀ τ ∈ twoSidedComplex G kX kY,
              (∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
                IsFPRASRun P₁ (initSlice m Δ G kX kY τ [ε, δ]) (timeC K d m ε δ)
                  (((twoSidedFacets G kX kY).filter (fun σ => τ ⊆ σ)).card : ℝ) ε δ) ∧
              (∀ ε : ℝ, 0 < ε → ε < 1 →
                IsFPAUSRun P₃ (initSlice m Δ G kX kY τ [ε]) (timeS K d m ε)
                  (fun S => condLaw (twoSidedFacets G kX kY) (twoSidedLaw G kX kY) τ (ofBits S)) ε)) ∧
          (∀ lam : ℝ, 0 < lam → lam ≤ c / Real.sqrt Δ → ∀ (b : Bool) (k : ℕ),
            (1 - γ Δ) * alphaStar Δ * m ≤ k → (k : ℝ) ≤ 4 * lam * m → ∀ τ ⊆ sideOf m b,
              (∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
                IsFPRASRun P₂ (initSlice m Δ G (if b then 1 else 0) k τ [lam, ε, δ]) (timeC K d m ε δ)
                  (facetMass ((sideOf m b).powersetCard k) (closedWeight G lam (sideOf m b) k) τ) ε δ) ∧
              (τ.card ≤ k → ∀ ε : ℝ, 0 < ε → ε < 1 →
                IsFPAUSRun P₄ (initSlice m Δ G (if b then 1 else 0) k τ [lam, ε]) (timeS K d m ε)
                  (fun S => condLaw ((sideOf m b).powersetCard k) (oneSidedLaw G lam (sideOf m b) k) τ (ofBits S))
                  ε))) := by sorry

end HardcoreSlices
