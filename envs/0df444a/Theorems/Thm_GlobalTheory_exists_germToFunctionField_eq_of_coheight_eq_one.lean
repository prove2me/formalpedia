-- Prove2me | Theorems.Thm_GlobalTheory_exists_germToFunctionField_eq_of_coheight_eq_one
-- name    : GlobalTheory.exists_germToFunctionField_eq_of_coheight_eq_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:50:07.819799+00:00
-- url     : https://prove2.me/theorems/ee6f34dd-ab63-486c-9d2d-bfc393ec6b0b
-- title:
--   Global Theory: exists germ To Function Field eq of coheight eq one
-- statement:
--   The Global Theory construction uses the exists germ To Function Field eq of coheight eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUniqueLbIsoPullEqOfCoheightLeOne.lean#L48-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUniqueLbIsoPullEqOfCoheightLeOne.lean#L48-L74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {X Y : Scheme.{u}}

theorem GlobalTheory.exists_germToFunctionField_eq_of_coheight_eq_one [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormalScheme X] (V : X.Opens) [Nonempty V] (t : X.functionField)
    (h : ∀ x ∈ V, Order.coheight x = 1 →
      t ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range) :
    ∃ s : Γ(X, V), X.germToFunctionField V s = t := by sorry
