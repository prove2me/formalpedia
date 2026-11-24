-- Prove2me | Theorems.Thm_GlobalTheory_NormSheafDescent_ideal_eq_top_of_forall_not_mem
-- name    : GlobalTheory.NormSheafDescent.ideal_eq_top_of_forall_not_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:41:59.821404+00:00
-- url     : https://prove2.me/theorems/6c8502d8-8ab2-4047-83ad-4264b3ec4881
-- title:
--   Norm Sheaf Descent: ideal eq top of forall not mem
-- statement:
--   The Norm Sheaf Descent construction uses the ideal eq top of forall not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormCoefficientIdealFamilyEqTopOfDisjoint.lean#L24-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormCoefficientIdealFamilyEqTopOfDisjoint.lean#L24-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FamIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormCoefficientIdealFamilyEqTopOfDisjoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.NormSheafDescent

theorem GlobalTheory.NormSheafDescent.ideal_eq_top_of_forall_not_mem {X : Scheme.{0}} (I : X.IdealSheafData) (V : X.affineOpens)
    (h : ∀ x ∈ I.support, x ∉ V.1) : I.ideal V = ⊤ := by sorry
