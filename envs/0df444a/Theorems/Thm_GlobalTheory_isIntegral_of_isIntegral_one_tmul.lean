-- Prove2me | Theorems.Thm_GlobalTheory_isIntegral_of_isIntegral_one_tmul
-- name    : GlobalTheory.isIntegral_of_isIntegral_one_tmul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:48:18.119935+00:00
-- url     : https://prove2.me/theorems/7f075c68-ab6c-57af-8daa-ecb63f1bb041
-- title:
--   Global Theory: is Integral of is Integral one tmul
-- statement:
--   The Global Theory construction uses the is Integral of is Integral one tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/IsIntegralIffMemSpanOneTmulIntegralClosure.lean#L64-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/IsIntegralIffMemSpanOneTmulIntegralClosure.lean#L64-L90

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

theorem GlobalTheory.isIntegral_of_isIntegral_one_tmul {R R' F F' : Type} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [IsLocalHom (algebraMap R R')]
    [Field F] [Algebra R F] [IsFractionRing R F] [Field F'] [Algebra R' F'] [IsFractionRing R' F']
    [Algebra F F'] [Algebra R F'] [IsScalarTower R F F'] [IsScalarTower R R' F']
    {L : Type} [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra R L] [IsScalarTower R F L]
    {l : L} (h : IsIntegral R' ((1 : F') ⊗ₜ[F] l)) : IsIntegral R l := by sorry
