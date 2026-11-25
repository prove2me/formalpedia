-- Prove2me | Theorems.Thm_GlobalTheory_exists_hasProjectiveDimensionLE_of_isRegularLocalRing
-- name    : GlobalTheory.exists_hasProjectiveDimensionLE_of_isRegularLocalRing
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:01:16.671271+00:00
-- url     : https://prove2.me/theorems/28f30aed-8da8-4d1d-9158-ff63bfbce605
-- title:
--   Global Theory: exists has Projective Dimension LE of is Regular Local Ring
-- statement:
--   The Global Theory construction uses the exists has Projective Dimension LE of is Regular Local Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsHasProjectiveDimensionLEOfResidueField.lean#L78-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsHasProjectiveDimensionLEOfResidueField.lean#L78-L82

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

theorem GlobalTheory.exists_hasProjectiveDimensionLE_of_isRegularLocalRing :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (M : Type) [AddCommGroup M] [Module R M]
      [Module.Finite R M], ∃ n : ℕ, HasProjectiveDimensionLE (ModuleCat.of R M) n := by sorry
