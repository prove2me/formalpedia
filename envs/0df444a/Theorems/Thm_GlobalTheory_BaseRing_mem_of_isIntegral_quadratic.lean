-- Prove2me | Theorems.Thm_GlobalTheory_BaseRing_mem_of_isIntegral_quadratic
-- name    : GlobalTheory.BaseRing.mem_of_isIntegral_quadratic
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:00:37.588347+00:00
-- url     : https://prove2.me/theorems/638ec126-2271-4163-b846-7ab0b30a4304
-- title:
--   Base Ring: mem of is Integral quadratic
-- statement:
--   The Base Ring construction uses the mem of is Integral quadratic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CmModelCoefficientSubringDedekindCompatibleEmbed.lean#L86-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CmModelCoefficientSubringDedekindCompatibleEmbed.lean#L86-L95

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

theorem GlobalTheory.BaseRing.mem_of_isIntegral_quadratic {d : ℕ} (hd : d.Prime) (hd4 : d % 4 = 3) {r : ℂ}
    (hr : r ^ 2 = -(d : ℂ)) (T : Subring ℂ) (hT : (1 + r) / 2 ∈ T) {z : ℂ} (hzK : z ∈ ℚ⟮r⟯)
    (hz : IsIntegral ℤ z) : z ∈ T := by sorry
