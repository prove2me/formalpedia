-- Prove2me | Theorems.Thm_NestedLogitFPTAS_lemma_4_2
-- name    : NestedLogitFPTAS.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:27:48.393445+00:00
-- url     : https://prove2.me/theorems/3ccd8a22-22c3-4816-a56f-9c76f5384388
-- title:
--   Lemma 4.2, p.19 (corrected: $G$ over nonempty subsets) — the computed set lies in $\mathcal N_{(2\delta_\omega,20\delta_\rho)}$
-- statement:
--   Let $\delta_\rho\in(0,1]$, $\delta_\omega\in(0,\delta_\rho/(8\gamma^+)]$ and $\omega_k,\rho_k>0$. If the single-nest algorithm returns a set $T$, then
--   $$
--   T\in\mathcal N_{(2\delta_\omega,20\delta_\rho)}(k,\omega_k,\rho_k).
--   $$
--   This bounds the infeasibility of the set that the rounded dynamic program finds.
--
--   Differences from the source:
--   - encoding: products in pairwise-disjoint nests N₁, …, N_M; assortments S = (S₁, …, S_M); non-negative γₘ → Fin n with nest : Fin n → Fin M; S : Finset (Fin n) with Sₘ = part S m; 0 < M, nonempty nests, 0 < γₘ; reason: same instances wherever the paper is defined: at γₘ = 0 the ratio γ⁺/γ⁻ and the power ωₖ^{1/γₖ} are undefined, and W↓, r_min, π_min minimize over Nₘ
--   - reading: Rₖ(T) ∈ (1 ± δρ)·ρₖ/w₊(T)^{γₖ}, undefined at T = ∅ → Rₖ(T)·w₊(T)^{γₖ} ∈ (1 ± δρ)·ρₖ, and ∅ is a member exactly when ωₖ = ρₖ = 0; reason: §4.1 calls the zero cases trivial; this agrees with (P₂), (P₃), and Lean's x/0 = 0 would put ∅ in N(k, 0, ρₖ) for ρₖ > 0
--   - correction: G over all subsets S ⊆ {1, …, t}; the search may return ∅ → the search reads G over nonempty subsets (an extra table); the recursion starts at t = 0; reason: one product with w = 0.05, r = 12, c = 1, w₀ₖ = 1, γₖ = 1, ωₖ = ρₖ = 1, δρ = 1/2, δω = 1/16: the neighbourhood is nonempty, but (η, ζ) = (0, 0) has G = 0, and ∅ is outside N_(2δω,20δρ)
-- source:
--   Segev, Approximation Schemes for Capacity-Constrained Assortment Optimization under the Nested Logit Model, SSRN #3553264 (Mar 2020), Lemma 4.2, p.19; proof in Appendix A.4

import Mathlib
import Definitions.Def_NestedLogitFPTAS_Model
import Definitions.Def_NestedLogitFPTAS_Neighbourhood
import Definitions.Def_NestedLogitFPTAS_SingleNest

namespace NestedLogitFPTAS

/-- Segev, SSRN #3553264 (Mar 2020), Lemma 4.2, p.19 (proof in Appendix A.4), **corrected**: a set returned by
`A(k, ωk, ρk)` lies in `N_(2δω,20δρ)(k, ωk, ρk)`.

**Formalization Note.** The search reads `G` over **nonempty** subsets; see `GCell` for the
counterexample to the printed algorithm at `δρ ≥ 1/3`. -/
theorem lemma_4_2 {n M : ℕ} (I : Instance n M) (hI : I.Standing) {δω δρ ωk ρk : ℝ} (k : Fin M)
    (hδρ : 0 < δρ) (hδρ1 : δρ ≤ 1) (hδω : 0 < δω)
    (hδω' : δω ≤ δρ / (8 * I.gammaPlus))
    (hωk : 0 < ωk) (hρk : 0 < ρk) {T : Finset (Fin n)}
    (hT : I.Aset δω δρ k ωk ρk = some T) :
    I.InNbhd (2 * δω) (20 * δρ) k ωk ρk T := by sorry

end NestedLogitFPTAS
