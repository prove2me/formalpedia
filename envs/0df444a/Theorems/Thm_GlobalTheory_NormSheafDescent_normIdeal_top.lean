-- Prove2me | Theorems.Thm_GlobalTheory_NormSheafDescent_normIdeal_top
-- name    : GlobalTheory.NormSheafDescent.normIdeal_top
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:42:06.568382+00:00
-- url     : https://prove2.me/theorems/277b7196-1d87-4449-9acb-8c9b61933198
-- title:
--   Norm Sheaf Descent: norm Ideal top
-- statement:
--   The Norm Sheaf Descent construction uses the norm Ideal top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormCoefficientIdealFamilyEqTopOfDisjoint.lean#L11-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormCoefficientIdealFamilyEqTopOfDisjoint.lean#L11-L22

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
open MvPolynomial

theorem GlobalTheory.NormSheafDescent.normIdeal_top (A K L B : Type) [CommRing A] [Field K] [Field L] [Algebra A K] [Algebra K L]
    [FiniteDimensional K L] [CommRing B] [Algebra B L] :
    GlobalTheory.NormSheaf.normIdeal A K L B (⊤ : Ideal B) = ⊤ := by sorry
