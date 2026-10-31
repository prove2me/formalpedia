-- Prove2me | Theorems.Thm_NestedLogitFPTAS_lemma_4_1
-- name    : NestedLogitFPTAS.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:27:32.077746+00:00
-- url     : https://prove2.me/theorems/408c81a8-3ec0-48e0-93ec-49e16ac1a812
-- title:
--   Lemma 4.1, p.18 — bounds on $\lambda(T)$ in the neighbourhood
-- statement:
--   Let $\delta_\rho\in(0,1]$, $\delta_\omega\in(0,\delta_\rho/(8\gamma^+)]$ and $\omega_k,\rho_k>0$. For every $T\in\mathcal N_{(\delta_\omega,\delta_\rho)}(k,\omega_k,\rho_k)$,
--   $$
--   (1-2\delta_\rho)\cdot\frac{\rho_k}{\omega_k^{1-1/\gamma_k}}\le\lambda(T)\le(1+3\delta_\rho)\cdot\frac{\rho_k}{\omega_k^{1-1/\gamma_k}} .
--   $$
--   Since $\lambda$ is additive over products, this turns the revenue constraint of the neighbourhood into a knapsack constraint.
--
--   Differences from the source:
--   - encoding: products in pairwise-disjoint nests N₁, …, N_M; assortments S = (S₁, …, S_M); non-negative γₘ → Fin n with nest : Fin n → Fin M; S : Finset (Fin n) with Sₘ = part S m; 0 < M, nonempty nests, 0 < γₘ; reason: same instances wherever the paper is defined: at γₘ = 0 the ratio γ⁺/γ⁻ and the power ωₖ^{1/γₖ} are undefined, and W↓, r_min, π_min minimize over Nₘ
--   - reading: Rₖ(T) ∈ (1 ± δρ)·ρₖ/w₊(T)^{γₖ}, undefined at T = ∅ → Rₖ(T)·w₊(T)^{γₖ} ∈ (1 ± δρ)·ρₖ, and ∅ is a member exactly when ωₖ = ρₖ = 0; reason: §4.1 calls the zero cases trivial; this agrees with (P₂), (P₃), and Lean's x/0 = 0 would put ∅ in N(k, 0, ρₖ) for ρₖ > 0
-- source:
--   Segev, Approximation Schemes for Capacity-Constrained Assortment Optimization under the Nested Logit Model, SSRN #3553264 (Mar 2020), Lemma 4.1, p.18; proof in Appendix A.3

import Mathlib
import Definitions.Def_NestedLogitFPTAS_Model
import Definitions.Def_NestedLogitFPTAS_Neighbourhood

namespace NestedLogitFPTAS

/-- Segev, SSRN #3553264 (Mar 2020), Lemma 4.1, p.18 (proof in Appendix A.3): for `T` in the
`(δω,δρ)`-neighbourhood, `(1 - 2δρ)·ρk/ωk^{1-1/γk} ≤ λ(T) ≤ (1 + 3δρ)·ρk/ωk^{1-1/γk}`.

**Formalization Note.** `ωk, ρk > 0` is the standing assumption of §4.1, and the bounds on `δρ`, `δω`
are those of Theorem 3.1, in whose proof the lemma sits. -/
theorem lemma_4_1 {n M : ℕ} (I : Instance n M) (hI : I.Standing) {δω δρ ωk ρk : ℝ} (k : Fin M)
    (hδρ : 0 < δρ) (hδρ1 : δρ ≤ 1) (hδω : 0 < δω)
    (hδω' : δω ≤ δρ / (8 * I.gammaPlus))
    (hωk : 0 < ωk) (hρk : 0 < ρk) {T : Finset (Fin n)} (hT : I.InNbhd δω δρ k ωk ρk T) :
    (1 - 2 * δρ) * ρk / ωk ^ (1 - 1 / I.γ k) ≤ I.lam T ∧
      I.lam T ≤ (1 + 3 * δρ) * ρk / ωk ^ (1 - 1 / I.γ k) := by sorry

end NestedLogitFPTAS
