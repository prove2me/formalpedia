-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_CFac_mulLC_apply
-- name    : GlobalTheory.LocFlat.CFac.mulLC_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:00.783805+00:00
-- url     : https://prove2.me/theorems/088d93ba-0148-468b-8468-0f3925851c54
-- title:
--   CFac: mul LC apply
-- statement:
--   The CFac construction uses the mul LC apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ProdFnMemSB.lean#L40-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ProdFnMemSB.lean#L40-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ProdFnMemSB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SplitWeil
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.CFac

theorem GlobalTheory.LocFlat.CFac.mulLC_apply {X : Type} [TopologicalSpace X] (φ : X → ℂ) (hφ : IsLocallyConstant φ) (F : SB X) (x : X) :
    (mulLC φ hφ F).1 x = φ x * F.1 x := by sorry

attribute [defeq] GlobalTheory.LocFlat.CFac.mulLC_apply
