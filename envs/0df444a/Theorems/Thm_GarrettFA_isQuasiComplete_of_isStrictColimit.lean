-- Prove2me | Theorems.Thm_GarrettFA_isQuasiComplete_of_isStrictColimit
-- name    : GarrettFA.isQuasiComplete_of_isStrictColimit
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T19:34:04.25919+00:00
-- url     : https://prove2.me/theorems/cc525e6d-2695-4345-a705-dc738657d31a
-- title:
--   Prop. 4.0.3 — strict colimits of quasi-complete spaces are quasi-complete
-- statement:
--   Let $V$ be the strict colimit of a chain of closed subspaces $V_0\subsetneq V_1\subsetneq\cdots$ (over $\mathbb K=\mathbb R$ or $\mathbb C$). If every $V_n$, with the subspace topology, is quasi-complete, then $V$ is quasi-complete.
--
--   In particular every LF-space is quasi-complete.
-- source:
--   Paul Garrett, *Completeness and quasi-completeness* (lecture notes, April 24, 2014), http://www.math.umn.edu/~garrett/m/fun/notes_2012-13/07d_quasi-completeness.pdf, p. 6, Proposition 4.0.3

import Definitions.Def_GarrettFA_IsStrictColimit
import Definitions.Def_GarrettFA_IsQuasiComplete

namespace GarrettFA
theorem isQuasiComplete_of_isStrictColimit {𝕜 : Type*} [RCLike 𝕜] {V : Type*} [AddCommGroup V] [Module 𝕜 V] [Module ℝ V]
    [IsScalarTower ℝ 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V]
    [T2Space V] {F : ℕ → Submodule 𝕜 V} (hF : IsStrictColimit 𝕜 F)
    (hq : ∀ n, IsQuasiComplete 𝕜 (F n)) :
    IsQuasiComplete 𝕜 V := by sorry
end GarrettFA
