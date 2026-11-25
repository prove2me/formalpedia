-- Prove2me | Theorems.Thm_GlobalTheory_CoeffRings_isIntegral_int_zeta
-- name    : GlobalTheory.CoeffRings.isIntegral_int_zeta
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:00:37.305829+00:00
-- url     : https://prove2.me/theorems/3ce8f712-5401-40a5-a4ff-1f9cd7472c6f
-- title:
--   Coeff Rings: is Integral int zeta
-- statement:
--   The Coeff Rings construction uses the is Integral int zeta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CoefficientFieldIntegersDedekindFractionField.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CoefficientFieldIntegersDedekindFractionField.lean#L29-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsDiscreteValuationRingAndFiniteResidueFieldValu
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_SqrtNegDiscMemCoeffField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CoefficientFieldIntegersDedekindFractionField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory GlobalTheory.CoeffRings
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.CoeffRings.isIntegral_int_zeta {n : ℕ} (hn : 0 < n) : IsIntegral ℤ (zeta n) := by sorry
