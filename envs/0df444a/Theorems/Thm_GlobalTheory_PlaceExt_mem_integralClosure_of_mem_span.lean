-- Prove2me | Theorems.Thm_GlobalTheory_PlaceExt_mem_integralClosure_of_mem_span
-- name    : GlobalTheory.PlaceExt.mem_integralClosure_of_mem_span
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:51:50.430815+00:00
-- url     : https://prove2.me/theorems/209857ab-3f7d-4452-9872-e7084077be7e
-- title:
--   Place Ext: mem integral Closure of mem span
-- statement:
--   The Place Ext construction uses the mem integral Closure of mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MemIntegralClosureOfMemSpan.lean#L224-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/MemIntegralClosureOfMemSpan.lean#L224-L272

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

theorem GlobalTheory.PlaceExt.mem_integralClosure_of_mem_span (l : L)
    (hl : (1 : F') ⊗ₜ[F] l ∈ Submodule.span R'
      ((fun b : L => (1 : F') ⊗ₜ[F] b) '' (integralClosure R L : Set L))) :
    l ∈ integralClosure R L := by sorry
