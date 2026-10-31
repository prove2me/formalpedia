-- Prove2me | Theorems.Thm_NestedLogitFPTAS_lemma_3_6
-- name    : NestedLogitFPTAS.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:28:35.259468+00:00
-- url     : https://prove2.me/theorems/52a6b96d-6a1f-48cb-9093-865a6bf8668c
-- title:
--   Lemma 3.6, p.17 (corrected: grids $\mathcal D_\omega$, $\mathcal D_\rho$) — the rounded path is admissible for (4)
-- statement:
--   Let $\epsilon>0$ and let $S$ be an assortment. For every nest $1\le k\le M$:
--
--   1. $\omega_k^*+\omega_{>k}^*\le\omega_{>k-1}^*$;
--   2. $\rho_k^*+\rho_{>k}^*\ge\rho_{>k-1}^*$;
--   3. $\mathcal A(k,\omega_k^*,\rho_k^*)\le c(S_k)$.
--
--   Hence the rounded path is a sequence of states and choices the program may traverse, and it certifies an upper bound on $\tilde F(1,\omega^*,\rho^*)$.
--
--   Differences from the source:
--   - encoding: products in pairwise-disjoint nests N₁, …, N_M; assortments S = (S₁, …, S_M); non-negative γₘ → Fin n with nest : Fin n → Fin M; S : Finset (Fin n) with Sₘ = part S m; 0 < M, nonempty nests, 0 < γₘ; reason: same instances wherever the paper is defined: at γₘ = 0 the ratio γ⁺/γ⁻ and the power ωₖ^{1/γₖ} are undefined, and W↓, r_min, π_min minimize over Nₘ
--   - encoding: any ϵ > 0 in the parameters ξω, ξρ, δω, δρ → the program uses ϵ̂ = min(ϵ, 1) in all its parameters; reason: no change for ϵ ≤ 1; the parameters need ϵ ≤ 80 and for ϵ ≥ 1 the guarantee is empty
--   - correction: Dω with p ≤ γ⁺·log_{1+ξω}(W↑/W↓); Dρ from π_min r_min W↓^{γ⁺} with q ≤ γ⁺·log_{1+ξρ}((r_max/(π_min r_min))(W↑/W↓)) → Pω = ⌈(γ⁺ log(W↑/W↓) + log M)/log(1+ξω)⌉ + M + 1; Lρ = (1−ξρ)^M π_min r_min W↓^{γ⁺}; Qρ = ⌈log(M r_max W↑^{γ⁺}/Lρ)/log(1+ξρ)⌉; reason: the printed tops cover one nest but the states hold sums: M = 2, one product per nest, r = w = c = 1, γ = 1, w₀ₘ = 0, w₀ = 2, C = 2 gives Dω = Dρ = {0, 1}, so R(S̃) ≤ 1/3 < (1−ϵ)/2 for ϵ < 1/3; and the printed bottom rounds (1−ξρ)·1 down to 0 there, so A(1, ω*₁, 0) = ∞ > c(S₁)
--   - correction: G over all subsets S ⊆ {1, …, t}; the search may return ∅ → the search reads G over nonempty subsets (an extra table); the recursion starts at t = 0; reason: one product with w = 0.05, r = 12, c = 1, w₀ₖ = 1, γₖ = 1, ωₖ = ρₖ = 1, δρ = 1/2, δω = 1/16: the neighbourhood is nonempty, but (η, ζ) = (0, 0) has G = 0, and ∅ is outside N_(2δω,20δρ)
--   - generalization: S an optimal dual assortment → every assortment S; reason: the proof uses no property of the dual optimum
--   - generalization: signs of c, C, w₀ are not stated; w₀ read as a positive weight → c and C real of any sign, w₀ ≥ 0, w₀ₘ ≥ 0; R(∅) = 0 at w₀ = 0; reason: the proofs use no sign of c or C, and every instance with nonnegative costs and positive w₀ is covered
-- source:
--   Segev, Approximation Schemes for Capacity-Constrained Assortment Optimization under the Nested Logit Model, SSRN #3553264 (Mar 2020), Lemma 3.6, p.17; proof in Appendix A.2

import Mathlib
import Definitions.Def_NestedLogitFPTAS_Model
import Definitions.Def_NestedLogitFPTAS_Grids
import Definitions.Def_NestedLogitFPTAS_SingleNest
import Definitions.Def_NestedLogitFPTAS_RoundedPath

namespace NestedLogitFPTAS

/-- Segev, SSRN #3553264 (Mar 2020), Lemma 3.6, p.17 (proof in Appendix A.2): for every nest,
(1) `ω*ₖ + ω*>ₖ ≤ ω*>ₖ₋₁`, (2) `ρ*ₖ + ρ*>ₖ ≥ ρ*>ₖ₋₁`, (3) `A(k, ω*ₖ, ρ*ₖ) ≤ c(Sₖ)`.

**Formalization Note.** Nest `k : Fin M` is the paper's `k + 1`, so `omegaStarAbove ε S k` is
`ω*>ₖ₋₁` and `omegaStarAbove ε S (k + 1)` is `ω*>ₖ`. With the corrected grids. The lemma holds for
every assortment `S`, not only for a dual optimum. `A` runs at the accuracy levels of p.13. -/
theorem lemma_3_6 {n M : ℕ} (I : Instance n M) (hI : I.Standing) {ε : ℝ} (hε : 0 < ε)
    (S : Finset (Fin n)) (k : Fin M) :
    I.omegaStar ε S k + I.omegaStarAbove ε S (k.val + 1) ≤ I.omegaStarAbove ε S k ∧
      I.rhoStarAbove ε S k ≤ I.rhoStar ε S k + I.rhoStarAbove ε S (k.val + 1) ∧
      I.Acost (I.deltaOmega ε) (I.deltaRho ε) k (I.omegaStar ε S k) (I.rhoStar ε S k) ≤
        ((I.cost (I.part S k) : ℝ) : WithTop ℝ) := by sorry

end NestedLogitFPTAS
