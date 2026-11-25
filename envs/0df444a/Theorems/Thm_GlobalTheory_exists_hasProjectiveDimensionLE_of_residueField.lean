-- Prove2me | Theorems.Thm_GlobalTheory_exists_hasProjectiveDimensionLE_of_residueField
-- name    : GlobalTheory.exists_hasProjectiveDimensionLE_of_residueField
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:01:21.8226+00:00
-- url     : https://prove2.me/theorems/f2f72496-fdb6-40d6-ad76-84db9fda8d3b
-- title:
--   Global Theory: exists has Projective Dimension LE of residue Field
-- statement:
--   The Global Theory construction uses the exists has Projective Dimension LE of residue Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsHasProjectiveDimensionLEOfResidueField.lean#L21-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsHasProjectiveDimensionLEOfResidueField.lean#L21-L76

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

theorem GlobalTheory.exists_hasProjectiveDimensionLE_of_residueField (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    (hk : projectiveDimension (ModuleCat.of R (R ⧸ maximalIdeal R)) ≠ ⊤)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ n : ℕ, HasProjectiveDimensionLE (ModuleCat.of R M) n := by sorry
