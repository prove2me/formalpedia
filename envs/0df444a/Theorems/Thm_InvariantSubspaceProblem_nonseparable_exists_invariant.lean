-- Prove2me | Theorems.Thm_InvariantSubspaceProblem_nonseparable_exists_invariant
-- name    : InvariantSubspaceProblem.nonseparable_exists_invariant
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-11T17:22:03.508561+00:00
-- url     : https://prove2.me/theorems/0ab87ce8-034c-4474-ac33-5a927b274fc8
-- title:
--   Operators on non-separable spaces have closed invariant subspaces
-- statement:
--   Let $E$ be a complex normed space that is **not** separable, and let $T\colon E\to E$ be a bounded linear operator. Then $T$ has a non-trivial closed invariant subspace.
--
--   This is why the invariant subspace problem is posed only for separable spaces: for any $x\neq 0$ the closed linear span of the orbit $\{x, Tx, T^2x,\dots\}$ is a closed invariant subspace which is non-zero and separable, hence different from $E$.
-- source:
--   Open Problem Garden, 'Invariant subspace problem' (posted by tchow, 9 Feb 2009), http://www.openproblemgarden.org/op/invariant_subspace_problem (the problem is restricted to separable Hilbert spaces); Radjavi & Rosenthal, The invariant subspace problem, Math. Intelligencer 4 (1982) 33–37.

import Definitions.Def_InvariantSubspaceProblem_Defs

namespace InvariantSubspaceProblem

theorem nonseparable_exists_invariant (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (hE : ¬ TopologicalSpace.SeparableSpace E) (T : E →L[ℂ] E) :
    HasNontrivialClosedInvariantSubspace T := by sorry

end InvariantSubspaceProblem
