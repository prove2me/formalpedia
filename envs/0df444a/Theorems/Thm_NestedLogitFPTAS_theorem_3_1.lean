-- Prove2me | Theorems.Thm_NestedLogitFPTAS_theorem_3_1
-- name    : NestedLogitFPTAS.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:28:07.638653+00:00
-- url     : https://prove2.me/theorems/f53d12b5-3595-4711-a757-f82c4c558de8
-- title:
--   Theorem 3.1, p.11 (corrected: $G$ over nonempty subsets) — the single-nest algorithm
-- statement:
--   There is a universal constant $K$ such that the following holds for every instance, every nest $k$, every $\delta_\rho\in(0,1]$, $\delta_\omega\in(0,\delta_\rho/(8\gamma^+)]$ and $\omega_k,\rho_k\ge0$.
--
--   1. If $\mathcal N_{(\delta_\omega,\delta_\rho)}(k,\omega_k,\rho_k)\neq\emptyset$, the algorithm computes a set $T\in\mathcal N_{(2\delta_\omega,20\delta_\rho)}(k,\omega_k,\rho_k)$ with $c(T)\le\mathcal P_{\approx(\delta_\omega,\delta_\rho)}(k,\omega_k,\rho_k)$.
--   2. If that neighbourhood is empty, the algorithm either reports so or computes a set in $\mathcal N_{(2\delta_\omega,20\delta_\rho)}(k,\omega_k,\rho_k)$.
--   3. The algorithm uses at most $K|N_k|^3/(\delta_\omega\delta_\rho)$ operations.
--
--   This replaces the NP-hard exact single-nest problem by a polynomial step, at the price of the slightly larger neighbourhood.
--
--   Differences from the source:
--   - encoding: products in pairwise-disjoint nests N₁, …, N_M; assortments S = (S₁, …, S_M); non-negative γₘ → Fin n with nest : Fin n → Fin M; S : Finset (Fin n) with Sₘ = part S m; 0 < M, nonempty nests, 0 < γₘ; reason: same instances wherever the paper is defined: at γₘ = 0 the ratio γ⁺/γ⁻ and the power ωₖ^{1/γₖ} are undefined, and W↓, r_min, π_min minimize over Nₘ
--   - reading: Rₖ(T) ∈ (1 ± δρ)·ρₖ/w₊(T)^{γₖ}, undefined at T = ∅ → Rₖ(T)·w₊(T)^{γₖ} ∈ (1 ± δρ)·ρₖ, and ∅ is a member exactly when ωₖ = ρₖ = 0; reason: §4.1 calls the zero cases trivial; this agrees with (P₂), (P₃), and Lean's x/0 = 0 would put ∅ in N(k, 0, ρₖ) for ρₖ > 0
--   - correction: G over all subsets S ⊆ {1, …, t}; the search may return ∅ → the search reads G over nonempty subsets (an extra table); the recursion starts at t = 0; reason: one product with w = 0.05, r = 12, c = 1, w₀ₖ = 1, γₖ = 1, ωₖ = ρₖ = 1, δρ = 1/2, δω = 1/16: the neighbourhood is nonempty, but (η, ζ) = (0, 0) has G = 0, and ∅ is outside N_(2δω,20δρ)
--   - reading: running time of "our algorithm", no machine model; arithmetic operations and table accesses are counted in §3.4, §4.2 → operations charged in the instrumented program: unit-cost +, −, ×, /, ≤, ⌊·⌋, ⌈·⌉, Real.rpow, Real.log and array accesses; reason: exact w₊^γ is irrational for rational data, so this is the accounting the paper performs
-- source:
--   Segev, Approximation Schemes for Capacity-Constrained Assortment Optimization under the Nested Logit Model, SSRN #3553264 (Mar 2020), Theorem 3.1, p.11; §4, pp.17–19

import Mathlib
import Definitions.Def_NestedLogitFPTAS_Model
import Definitions.Def_NestedLogitFPTAS_Neighbourhood
import Definitions.Def_NestedLogitFPTAS_SingleNest

namespace NestedLogitFPTAS

/-- Segev, SSRN #3553264 (Mar 2020), Theorem 3.1, p.11: the program `singleNest` is an
`O(|Nₖ|³/(δωδρ))` algorithm such that, if the `(δω,δρ)`-neighbourhood is nonempty, it computes a set of
`N_(2δω,20δρ)(k, ωk, ρk)` of cost at most `P≈_(δω,δρ)(k, ωk, ρk)`, and if it is empty, it either
reports so or computes a set of `N_(2δω,20δρ)(k, ωk, ρk)`.

**Formalization Note.** `O(·)` is one constant `K`, quantified before all the data (trap 8). The
statement covers all `ωk, ρk ≥ 0`, including the zero cases that §4.1 calls trivial and the DP uses. -/
theorem theorem_3_1 :
    ∃ K : ℝ, 0 < K ∧ ∀ {n M : ℕ} (I : Instance n M), I.Standing →
      ∀ (k : Fin M) (δω δρ ωk ρk : ℝ), 0 < δρ → δρ ≤ 1 → 0 < δω →
        δω ≤ δρ / (8 * I.gammaPlus) → 0 ≤ ωk → 0 ≤ ρk →
        ((I.Nbhd δω δρ k ωk ρk).Nonempty →
          ∃ T, I.Aset δω δρ k ωk ρk = some T ∧ I.InNbhd (2 * δω) (20 * δρ) k ωk ρk T ∧
            ((I.cost T : ℝ) : WithTop ℝ) ≤ I.Papprox δω δρ k ωk ρk) ∧
        (I.Nbhd δω δρ k ωk ρk = ∅ →
          I.Aset δω δρ k ωk ρk = none ∨
            ∃ T, I.Aset δω δρ k ωk ρk = some T ∧ I.InNbhd (2 * δω) (20 * δρ) k ωk ρk T) ∧
        (I.Aops δω δρ k ωk ρk : ℝ) ≤ K * ((I.nestSet k).card : ℝ) ^ 3 / (δω * δρ) := by sorry

end NestedLogitFPTAS
