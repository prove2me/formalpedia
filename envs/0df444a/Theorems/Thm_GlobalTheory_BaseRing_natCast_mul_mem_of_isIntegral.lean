-- Prove2me | Theorems.Thm_GlobalTheory_BaseRing_natCast_mul_mem_of_isIntegral
-- name    : GlobalTheory.BaseRing.natCast_mul_mem_of_isIntegral
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:00:28.562037+00:00
-- url     : https://prove2.me/theorems/e256ecd9-e3d3-4606-901b-611c7791308c
-- title:
--   Base Ring: nat Cast mul mem of is Integral
-- statement:
--   The Base Ring construction uses the nat Cast mul mem of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CmModelCoefficientSubringDedekindCompatibleEmbed.lean#L51-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CmModelCoefficientSubringDedekindCompatibleEmbed.lean#L51-L82

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IntOfPrimeMulSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CmModelCoefficientSubringDedekindCompatibleEmbed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.BaseRing
open Polynomial
open IntermediateField

theorem GlobalTheory.BaseRing.natCast_mul_mem_of_isIntegral (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (T : Subring ℂ) (hT : ∀ w ∈ K, IsIntegral ℤ w → w ∈ T) {ζ : ℂ} {n : ℕ} (hn : 0 < n)
    (hζ : ζ ^ n = 1) (hζT : ζ ∈ T) {z : ℂ} (hzK : z ∈ K⟮ζ⟯) (hz : IsIntegral ℤ z) :
    (n : ℂ) * z ∈ T := by sorry
