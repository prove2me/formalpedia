-- Prove2me | Theorems.Thm_GeneralizedUniformServer_UnitWeights_lazy_weight
-- name    : GeneralizedUniformServer.UnitWeights.lazy_weight
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:45:28.531802+00:00
-- url     : https://prove2.me/theorems/ab7f425e-f874-4e27-9481-65be98f80ae3
-- title:
--   Lemma 3.3 — a lazy path with $m$ moves retains weight $\Phi_T\ge\phi_T(\tilde o_T)\ge(2k)^{-m}$
-- statement:
--   Let $k\ge1$ and fix a finite request sequence $\rho=(r_1,\dots,r_T)$. If $\tilde o_0=a,\tilde o_1,\dots,\tilde o_T$ is a lazy offline solution for $\rho$ that moves $m$ times, then
--   $$\Phi_T\ \ge\ \phi_T(\tilde o_T)\ \ge\ (2k)^{-m}.$$
--
--   Together with Lemma 2.1 this gives $\Phi_T\ge(2k)^{-\mathrm{OPT}(\rho)}$, which turns the bound $(k+1)\ln(1/\Phi_T)$ of Lemma 3.2 into the competitive bound of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: configurations on pairwise disjoint spaces, finite request sequences and unit movement costs → dependent configurations indexed by `Fin k`, request lists with 0-based entries, finite schedules where used, and natural-valued Hamming costs and OPT; reason: tagged coordinates preserve each space, the list and schedule indices relabel the source times, and every unit-weight cost is a natural number, with OPT attained over the nonempty feasible set
--   - encoding: the bound $(2k)^{-m}$ → $((2k)^m)^{-1}$ in $\mathbb R_{\ge0}$, with $m$ the defined number of moves; reason: equal for $k\ge1$
-- source:
--   Junho Hwang, STOC 2027 submission #428 (October 2026), p. 9, Lemma 3.3

import Mathlib
import Definitions.Def_GeneralizedUniformServer_UnitWeights_Weights

open scoped NNReal

namespace GeneralizedUniformServer.UnitWeights

/-- Lemma 3.3 (source p. 9): if `õ₀ = a, õ₁, …, õ_T` is a lazy offline solution for
`ρ = (r₁, …, r_T)` that moves `m` times, then `Φ_T ≥ ϕ_T(õ_T) ≥ (2k)^{-m}`. -/
theorem lazy_weight {k : ℕ} [NeZero k] {M : Fin k → Type*}
    (a : Config M) (ρ : List (Config M)) (o : Fin (ρ.length + 1) → Config M)
    (hsol : IsOfflineSolution ρ o) (hlazy : IsLazy ρ o) (h₀ : o 0 = a) :
    weights a ρ (o (Fin.last ρ.length)) ≤ totalWeight a ρ ∧
      ((2 * (k : ℝ≥0)) ^ numMoves ρ o)⁻¹ ≤ weights a ρ (o (Fin.last ρ.length)) := by sorry

end GeneralizedUniformServer.UnitWeights
