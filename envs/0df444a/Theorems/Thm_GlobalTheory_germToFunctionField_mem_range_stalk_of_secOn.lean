-- Prove2me | Theorems.Thm_GlobalTheory_germToFunctionField_mem_range_stalk_of_secOn
-- name    : GlobalTheory.germToFunctionField_mem_range_stalk_of_secOn
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:48:18.535802+00:00
-- url     : https://prove2.me/theorems/622af867-2857-4fd9-85a4-dc01a2d67a3a
-- title:
--   Global Theory: germ To Function Field mem range stalk of sec On
-- statement:
--   The Global Theory construction uses the germ To Function Field mem range stalk of sec On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUniqueLbIsoPullEqOfCoheightLeOne.lean#L473-L486
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUniqueLbIsoPullEqOfCoheightLeOne.lean#L473-L486

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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y : Scheme.{0}}
variable [IsIntegral X]

theorem GlobalTheory.germToFunctionField_mem_range_stalk_of_secOn {L : LB X} {W : X.Opens}
    {s : ∀ i, Γ(X, W ⊓ L.U i)} (hs : s ∈ secOn L W) {x : X} {i j : L.ι} (hi : x ∈ L.U i)
    (hj : x ∈ L.U j) [Nonempty (W ⊓ L.U i : X.Opens)] [Nonempty (W ⊓ L.U j : X.Opens)]
    (h : X.germToFunctionField _ (s j) ∈
      (algebraMap (X.presheaf.stalk x) X.functionField).range) :
    X.germToFunctionField _ (s i) ∈ (algebraMap (X.presheaf.stalk x) X.functionField).range := by sorry
