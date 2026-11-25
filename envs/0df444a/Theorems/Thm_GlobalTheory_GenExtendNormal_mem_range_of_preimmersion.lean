-- Prove2me | Theorems.Thm_GlobalTheory_GenExtendNormal_mem_range_of_preimmersion
-- name    : GlobalTheory.GenExtendNormal.mem_range_of_preimmersion
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:52:52.764801+00:00
-- url     : https://prove2.me/theorems/604a5ec7-f63f-45ac-bd90-d73bec629389
-- title:
--   Gen Extend Normal: mem range of preimmersion
-- statement:
--   The Gen Extend Normal construction uses the mem range of preimmersion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueRigidifiedGeneratorExtendNormal.lean#L29-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueRigidifiedGeneratorExtendNormal.lean#L29-L59

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueGeneratorExtendDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueRigidifiedGeneratorExtendNormal
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.GenExtendNormal
open GlobalTheory.DvrModel

theorem GlobalTheory.GenExtendNormal.mem_range_of_preimmersion {H Y Z : Scheme.{0}} [IsIntegral H] (g : Y ⟶ H)
    [IsPreimmersion g] (k : Z ⟶ Y) (z : Z) (hz : g (k z) = genericPoint H) (y : Y)
    (A : H.Opens) [Nonempty A] (τ : Γ(H, A)) (O : Y.Opens) (hy : y ∈ O) (c : Γ(Y, O))
    (h : gs k z O c = gs (k ≫ g) z A τ) :
    H.germToFunctionField A τ ∈ (algebraMap (H.presheaf.stalk (g y)) H.functionField).range := by sorry
