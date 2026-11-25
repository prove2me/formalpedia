-- Prove2me | Theorems.Thm_GlobalTheory_exists_integral_point_through
-- name    : GlobalTheory.exists_integral_point_through
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:53:45.72415+00:00
-- url     : https://prove2.me/theorems/4ec2c783-4158-42dd-af0c-99612bd9ea18
-- title:
--   Global Theory: exists integral point through
-- statement:
--   The Global Theory construction uses the exists integral point through property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsIntegralPointThrough.lean#L11-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsIntegralPointThrough.lean#L11-L145

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DimensionQuotientBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PrimeAvoidanceFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsIntegralPointThrough
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.T0
open IsLocalRing

theorem GlobalTheory.exists_integral_point_through (O B : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B] [Module.Flat O B]
    (M : Ideal B) (hM : M.IsMaximal) (hsp : Ideal.map (algebraMap O B) (maximalIdeal O) ≤ M)
    (e : B) (he : e ≠ 0) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Algebra O V)
      (_ : Module.Finite O V) (φ : B →ₐ[O] V), φ e ≠ 0 ∧ ∀ x ∈ M, φ x ∈ maximalIdeal V := by sorry
