-- Prove2me | Theorems.Thm_GuardAugmentation_exists_near_coloring
-- name    : GuardAugmentation.exists_near_coloring
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:39:37.847871+00:00
-- url     : https://prove2.me/theorems/ab20565f-4fc1-4c53-aa59-9c76493e62e4
-- title:
--   One binary coloring matches an outgoing edge at all but one vertex
-- statement:
--   Let \(V\) be finite, and let \(R\) be a relation such that every pair of distinct vertices is related in at least one direction. For any Boolean edge labeling \(\ell\), there are a vertex coloring \(c\) and a set \(B\subseteq V\) with
--   \[
--   |B|\le1,\qquad
--   \forall x\notin B,\ \exists y:\ R(x,y)\ \text{and}\ \ell(x,y)=c(y).
--   \]
--   The statement also includes the empty vertex type. This coloring is used to absorb guard vertices while losing at most one vertex.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, GuardAugmentation, lines 76–97; source SHA256 9f7c8a76b829f98117ee0347abbe7f6abea6b1067f3dac3c6ba994ff5ed748fe.

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_GuardAugmentation
import Definitions.Def_Sensitivity213303_TournamentHighRows

namespace CandidateCoherence
end CandidateCoherence
namespace MinmaxLocal
end MinmaxLocal
namespace TournamentHighRows
end TournamentHighRows
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace GuardAugmentation
end GuardAugmentation
open GuardAugmentation
open scoped Classical
open Finset MinmaxLocal TournamentHighRows CandidateCoherence
variable {V X : Type} [Fintype V] [DecidableEq V]

theorem GuardAugmentation.exists_near_coloring (R : V → V → Prop)
    (ht : ∀ x y, x ≠ y → R x y ∨ R y x) (label : V → V → Bool) :
    ∃ (color : V → Bool) (bad : Finset V), bad.card ≤ 1 ∧
      ∀ x, x ∉ bad → ∃ y, R x y ∧ label x y = color y := by sorry
