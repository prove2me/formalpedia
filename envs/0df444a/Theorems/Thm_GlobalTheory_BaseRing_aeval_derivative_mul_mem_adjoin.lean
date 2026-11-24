-- Prove2me | Theorems.Thm_GlobalTheory_BaseRing_aeval_derivative_mul_mem_adjoin
-- name    : GlobalTheory.BaseRing.aeval_derivative_mul_mem_adjoin
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:59:44.500346+00:00
-- url     : https://prove2.me/theorems/a60f454b-df52-43ef-9e6a-192f67a60936
-- title:
--   Base Ring: aeval derivative mul mem adjoin
-- statement:
--   The Base Ring construction uses the aeval derivative mul mem adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CmModelCoefficientSubringDedekindCompatibleEmbed.lean#L15-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CmModelCoefficientSubringDedekindCompatibleEmbed.lean#L15-L47

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

theorem GlobalTheory.BaseRing.aeval_derivative_mul_mem_adjoin (A K : Type*) {L : Type*} [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsDomain A] [IsFractionRing A K]
    [IsIntegrallyClosed A] [FiniteDimensional K L] [Algebra.IsSeparable K L] {x : L}
    (hx : Algebra.adjoin K {x} = ⊤) (hAx : IsIntegral A x) (f : A[X]) (hf : aeval x f = 0)
    {z : L} (hz : IsIntegral A z) : aeval x (derivative f) * z ∈ Algebra.adjoin A {x} := by sorry
