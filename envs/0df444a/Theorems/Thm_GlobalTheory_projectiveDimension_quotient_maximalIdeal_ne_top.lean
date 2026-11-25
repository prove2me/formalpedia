-- Prove2me | Theorems.Thm_GlobalTheory_projectiveDimension_quotient_maximalIdeal_ne_top
-- name    : GlobalTheory.projectiveDimension_quotient_maximalIdeal_ne_top
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:02:19.78199+00:00
-- url     : https://prove2.me/theorems/9ec1c931-ce5d-407c-ac14-17b3371610c8
-- title:
--   Global Theory: projective Dimension quotient maximal Ideal ne top
-- statement:
--   The Global Theory construction uses the projective Dimension quotient maximal Ideal ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsHasProjectiveDimensionLEOfResidueField.lean#L11-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsHasProjectiveDimensionLEOfResidueField.lean#L11-L19

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsHasProjectiveDimensionLEOfResidueField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory IsLocalRing
open GlobalTheory
universe u

theorem GlobalTheory.projectiveDimension_quotient_maximalIdeal_ne_top (R : Type u) [CommRing R]
    [IsRegularLocalRing R] :
    projectiveDimension (ModuleCat.of R (R ⧸ maximalIdeal R)) ≠ ⊤ := by sorry
