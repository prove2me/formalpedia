-- Prove2me | Theorems.Thm_GlobalTheory_SquareZeroLeibnizPoint_sqzOfLeibniz_fst
-- name    : GlobalTheory.SquareZeroLeibnizPoint.sqzOfLeibniz_fst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:27.880685+00:00
-- url     : https://prove2.me/theorems/af3dd5de-c0b6-4669-b025-a53135c37b44
-- title:
--   Square Zero Leibniz Point: sqz Of Leibniz fst
-- statement:
--   The Square Zero Leibniz Point construction uses the sqz Of Leibniz fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/FstHomCompSqzOfLeibniz.lean#L73-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/FstHomCompSqzOfLeibniz.lean#L73-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FstHomCompSqzOfLeibniz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SquareZeroLeibnizPoint
open TrivSqZeroExt
variable {A O M : Type*} [CommRing A] [CommRing O] [AddCommGroup M] [Module O M]
variable [Module Oᵐᵒᵖ M] [IsCentralScalar O M]

theorem GlobalTheory.SquareZeroLeibnizPoint.sqzOfLeibniz_fst (ε : A →+* O) (d : A →+ M)
    (hd : ∀ f f', d (f * f') = ε f • d f' + ε f' • d f) (f : A) :
    (sqzOfLeibniz ε d hd f).fst = ε f := by sorry

attribute [defeq] GlobalTheory.SquareZeroLeibnizPoint.sqzOfLeibniz_fst
