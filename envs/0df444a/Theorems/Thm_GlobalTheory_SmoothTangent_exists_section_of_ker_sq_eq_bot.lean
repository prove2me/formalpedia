-- Prove2me | Theorems.Thm_GlobalTheory_SmoothTangent_exists_section_of_ker_sq_eq_bot
-- name    : GlobalTheory.SmoothTangent.exists_section_of_ker_sq_eq_bot
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:54:35.379328+00:00
-- url     : https://prove2.me/theorems/a28f8c4b-dd7e-44fe-92b9-df87e2e408eb
-- title:
--   Smooth Tangent: exists section of ker sq eq bot
-- statement:
--   The Smooth Tangent construction uses the exists section of ker sq eq bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothOfRelativeDimensionOfDimOfFinrankDerivatio.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothOfRelativeDimensionOfDimOfFinrankDerivatio.lean#L14-L18

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfDimOfFinrankDerivatio
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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.SmoothTangent

theorem GlobalTheory.SmoothTangent.exists_section_of_ker_sq_eq_bot {k B F : Type*} [CommRing k] [CommRing B] [CommRing F]
    [Algebra k B] [Algebra k F] [Algebra.FormallySmooth k F] (π : B →ₐ[k] F)
    (hπ : Function.Surjective π) (h : RingHom.ker π.toRingHom ^ 2 = ⊥) :
    ∃ g : F →ₐ[k] B, π.comp g = AlgHom.id k F := by sorry
