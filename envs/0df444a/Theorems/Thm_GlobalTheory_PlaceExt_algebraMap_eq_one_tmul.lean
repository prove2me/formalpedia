-- Prove2me | Theorems.Thm_GlobalTheory_PlaceExt_algebraMap_eq_one_tmul
-- name    : GlobalTheory.PlaceExt.algebraMap_eq_one_tmul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:26:20.6248+00:00
-- url     : https://prove2.me/theorems/46d8c7e5-fde1-4f80-b8ed-f29650821879
-- title:
--   Place Ext: algebra Map eq one tmul
-- statement:
--   The Place Ext construction uses the algebra Map eq one tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MemIntegralClosureOfMemSpan.lean#L277-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MemIntegralClosureOfMemSpan.lean#L277-L282

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MemIntegralClosureOfMemSpan
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
open GlobalTheory
open GlobalTheory.PlaceExt
variable {R R' : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R']
  [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')]
variable {F F' : Type} [Field F] [Algebra R F] [IsFractionRing R F] [Field F'] [Algebra R' F']
  [IsFractionRing R' F'] [Algebra F F'] [Algebra R F'] [IsScalarTower R F F']
  [IsScalarTower R R' F']
variable {L : Type} [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
  [Algebra R L] [IsScalarTower R F L]
omit [IsDomain R] [IsDiscreteValuationRing R] [IsDomain R'] [IsDiscreteValuationRing R']
  [IsLocalHom (algebraMap R R')] [IsFractionRing R F] [IsFractionRing R' F']
  [FiniteDimensional F L] [Algebra.IsSeparable F L]

theorem GlobalTheory.PlaceExt.algebraMap_eq_one_tmul (r : R) :
    algebraMap R' (F' ⊗[F] L) (algebraMap R R' r) = (1 : F') ⊗ₜ[F] algebraMap R L r := by sorry
