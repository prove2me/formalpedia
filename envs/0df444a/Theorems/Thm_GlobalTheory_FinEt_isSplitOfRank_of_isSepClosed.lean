-- Prove2me | Theorems.Thm_GlobalTheory_FinEt_isSplitOfRank_of_isSepClosed
-- name    : GlobalTheory.FinEt.isSplitOfRank_of_isSepClosed
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:10:26.811314+00:00
-- url     : https://prove2.me/theorems/e305ca3d-a5be-41ea-bc2c-a184dad70409
-- title:
--   Fin Et: is Split Of Rank of is Sep Closed
-- statement:
--   The Fin Et construction uses the is Split Of Rank of is Sep Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L633-L642
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoIffBijectiveOverAlgClosed.lean#L633-L642

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry
universe u
noncomputable section
open GlobalTheory GlobalTheory.FinEt
attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc
variable {S : Scheme.{u}} {X Y : Over S}

theorem GlobalTheory.FinEt.isSplitOfRank_of_isSepClosed {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsFinite p] [Etale p] (s : Spec (.of k)) :
    IsSplitOfRank p (p.finrank s) := by sorry
