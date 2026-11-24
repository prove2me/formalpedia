-- Prove2me | Theorems.Thm_GlobalTheory_NormSheafDescent_isField_stalk_of_forall_specializes
-- name    : GlobalTheory.NormSheafDescent.isField_stalk_of_forall_specializes
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:42:13.462187+00:00
-- url     : https://prove2.me/theorems/6d109c8e-6a96-47da-83c9-e16e349db7e5
-- title:
--   Norm Sheaf Descent: is Field stalk of forall specializes
-- statement:
--   The Norm Sheaf Descent construction uses the is Field stalk of forall specializes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFieldStalkImageOfGenericPoint.lean#L10-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFieldStalkImageOfGenericPoint.lean#L10-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FamIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFieldStalkImageOfGenericPoint
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

theorem GlobalTheory.NormSheafDescent.isField_stalk_of_forall_specializes {Z : Scheme.{0}} (ζ : Z) [IsDomain (Z.presheaf.stalk ζ)]
    (h : ∀ z : Z, z ⤳ ζ → z = ζ) : IsField (Z.presheaf.stalk ζ) := by sorry
