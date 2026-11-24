-- Prove2me | Theorems.Thm_GlobalTheory_DegKer_finrank_eq_pow_mul_card
-- name    : GlobalTheory.DegKer.finrank_eq_pow_mul_card
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:59:43.597228+00:00
-- url     : https://prove2.me/theorems/269577df-08da-46e7-868a-d83b1a24b8e9
-- title:
--   Deg Ker: finrank eq pow mul card
-- statement:
--   The Deg Ker construction uses the finrank eq pow mul card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MapDegreeEqExpCharPowMulCardKernel.lean#L18-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MapDegreeEqExpCharPowMulCardKernel.lean#L18-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsIntegralOfIsAbelianSchemeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MapDegreeEqExpCharPowMulCardKernel
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
open GlobalTheory.ZV
noncomputable section
open GlobalTheory
open GlobalTheory.DegKer

theorem GlobalTheory.DegKer.finrank_eq_pow_mul_card (R S Ω : Type) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    [Algebra R S] [Module.Finite R S] [FaithfulSMul R S] [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
    [FaithfulSMul R Ω] (p : ℕ) [ExpChar R p] :
    Nat.card (S →ₐ[R] Ω) ≠ 0 ∧ ∃ e : ℕ, Module.finrank R S = p ^ e * Nat.card (S →ₐ[R] Ω) := by sorry
