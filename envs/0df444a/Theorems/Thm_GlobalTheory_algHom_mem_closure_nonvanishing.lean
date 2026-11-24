-- Prove2me | Theorems.Thm_GlobalTheory_algHom_mem_closure_nonvanishing
-- name    : GlobalTheory.algHom_mem_closure_nonvanishing
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:06:35.003022+00:00
-- url     : https://prove2.me/theorems/ff19cdeb-82ed-4559-a9ed-706040f2c84e
-- title:
--   Global Theory: alg Hom mem closure nonvanishing
-- statement:
--   The Global Theory construction uses the alg Hom mem closure nonvanishing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/PrincipalOpenDenseComplexPoints.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/PrincipalOpenDenseComplexPoints.lean#L14-L23

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_PrincipalOpenDenseComplexPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open AffinePoints

theorem GlobalTheory.algHom_mem_closure_nonvanishing (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] (f : A) (hf : f ≠ 0) :
    {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x 1 ≠ 0} ⊆
      closure {x : A → ℂ | ∃ φ : A →ₐ[ℂ] ℂ, ⇑φ = x ∧ x f ≠ 0} := by sorry
