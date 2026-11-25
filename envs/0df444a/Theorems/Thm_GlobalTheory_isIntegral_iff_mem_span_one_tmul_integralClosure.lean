-- Prove2me | Theorems.Thm_GlobalTheory_isIntegral_iff_mem_span_one_tmul_integralClosure
-- name    : GlobalTheory.isIntegral_iff_mem_span_one_tmul_integralClosure
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:58:50.553354+00:00
-- url     : https://prove2.me/theorems/4355e706-1905-4be7-a2d6-571a05656149
-- title:
--   Global Theory: is Integral iff mem span one tmul integral Closure
-- statement:
--   The Global Theory construction uses the is Integral iff mem span one tmul integral Closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/IsIntegralIffMemSpanOneTmulIntegralClosure.lean#L211-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/IsIntegralIffMemSpanOneTmulIntegralClosure.lean#L211-L337

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsIntegralIffMemSpanOneTmulIntegralClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open Polynomial
open GlobalTheory
open NumberField
open scoped TensorProduct
open Polynomial

theorem GlobalTheory.isIntegral_iff_mem_span_one_tmul_integralClosure :
    ∀ (R R' F F' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [Module.Flat R R'] [IsLocalHom (algebraMap R R')] [Field F] [Algebra R F] [IsFractionRing R F] [Field F'] [Algebra R' F'] [IsFractionRing R' F'] [Algebra F F'] [Algebra R F'] [IsScalarTower R F F'] [IsScalarTower R R' F'], Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' → Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R R')) → ∀ (L : Type) [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L] [Algebra R L] [IsScalarTower R F L] (x : F' ⊗[F] L), IsIntegral R' x ↔ x ∈ Submodule.span R' ((fun b : L => (1 : F') ⊗ₜ[F] b) '' (integralClosure R L : Set L)) := by sorry
