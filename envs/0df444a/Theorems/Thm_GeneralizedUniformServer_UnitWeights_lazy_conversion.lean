-- Prove2me | Theorems.Thm_GeneralizedUniformServer_UnitWeights_lazy_conversion
-- name    : GeneralizedUniformServer.UnitWeights.lazy_conversion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:44:38.592208+00:00
-- url     : https://prove2.me/theorems/edb67dcd-3619-43da-825d-173e2a49eb18
-- title:
--   Lemma 2.1 — any offline solution yields a lazy one from an arbitrary start
-- statement:
--   With unit weights, let $\rho=(r_1,\dots,r_T)$ be a finite request sequence, let $o_0,\dots,o_T$ be an offline solution for $\rho$ of cost $C=\sum_{t=1}^T d(o_{t-1},o_t)$, and let $a$ be any configuration. Then there is a lazy offline solution $\tilde o_0,\dots,\tilde o_T$ with $\tilde o_0=a$ whose number of moves satisfies
--   $$\bigl|\{t\in[T]:\tilde o_t\ne\tilde o_{t-1}\}\bigr|\le C+d(a,o_0).$$
--
--   Applied to an optimal solution from $a$, it gives a lazy solution from $a$ that moves at most $\mathrm{OPT}(\rho)$ times, the input to Lemma 3.3 in the proof of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: configurations on pairwise disjoint spaces, finite request sequences and unit movement costs → dependent configurations indexed by `Fin k`, request lists with 0-based entries, finite schedules where used, and natural-valued Hamming costs and OPT; reason: tagged coordinates preserve each space, the list and schedule indices relabel the source times, and every unit-weight cost is a natural number, with OPT attained over the nonempty feasible set
--   - encoding: the cost $C$ of the given solution → the term `offlineCost ρ o` substituted for $C$; reason: $C$ is defined as that cost, so no instance changes
-- source:
--   Junho Hwang, STOC 2027 submission #428 (October 2026), p. 8, Lemma 2.1

import Mathlib
import Definitions.Def_GeneralizedUniformServer_UnitWeights_Model

namespace GeneralizedUniformServer.UnitWeights

/-- Lemma 2.1 (source p. 8): with unit weights, let `o₀, …, o_T` be an offline solution of
cost `C` and let `a` be any configuration. There is a lazy offline solution with `õ₀ = a`
that moves at most `C + d(a, o₀)` times. -/
theorem lazy_conversion {k : ℕ} [NeZero k] {M : Fin k → Type*}
    (ρ : List (Config M)) (o : Fin (ρ.length + 1) → Config M)
    (ho : IsOfflineSolution ρ o) (a : Config M) :
    ∃ o' : Fin (ρ.length + 1) → Config M,
      IsOfflineSolution ρ o' ∧ IsLazy ρ o' ∧ o' 0 = a ∧
        numMoves ρ o' ≤ offlineCost ρ o + dist a (o 0) := by sorry

end GeneralizedUniformServer.UnitWeights
