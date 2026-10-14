-- Prove2me | Theorems.Thm_GarrettFA_isQuasiComplete_submodule_of_isClosed
-- name    : GarrettFA.isQuasiComplete_submodule_of_isClosed
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T19:33:10.305977+00:00
-- url     : https://prove2.me/theorems/3ae34399-e81e-48c1-8536-90fa0c288426
-- title:
--   §4 — closed subspaces of quasi-complete spaces are quasi-complete
-- statement:
--   Let $V$ be a quasi-complete topological vector space over $\mathbb K=\mathbb R$ or $\mathbb C$ and $W\subseteq V$ a closed linear subspace. Then $W$, with the subspace topology, is quasi-complete.
-- source:
--   Paul Garrett, *Completeness and quasi-completeness* (lecture notes, April 24, 2014), http://www.math.umn.edu/~garrett/m/fun/notes_2012-13/07d_quasi-completeness.pdf, p. 6, remark after Definition 4.0.2 ("closed subspaces of quasi-complete spaces are quasi-complete")

import Definitions.Def_GarrettFA_IsQuasiComplete

namespace GarrettFA
theorem isQuasiComplete_submodule_of_isClosed {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [Module ℝ V]
    [IsScalarTower ℝ 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V]
    [T2Space V]
    (hV : IsQuasiComplete 𝕜 V) (W : Submodule 𝕜 V) (hW : IsClosed (W : Set V)) :
    IsQuasiComplete 𝕜 W := by sorry
end GarrettFA
