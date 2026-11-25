-- Prove2me | Theorems.Thm_GlobalTheory_VerticalGauss_finite_places
-- name    : GlobalTheory.VerticalGauss.finite_places
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:54:08.799987+00:00
-- url     : https://prove2.me/theorems/1f05b19f-24ff-478e-a602-7f1c2d611650
-- title:
--   Vertical Gauss: finite places
-- statement:
--   The Vertical Gauss construction uses the finite places property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/FiniteVerticalGaussValuations.lean#L118-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/FiniteVerticalGaussValuations.lean#L118-L145

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_FiniteVerticalGaussValuations
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
open GlobalTheory.VerticalGauss
open IsLocalRing IsDedekindDomain

theorem GlobalTheory.VerticalGauss.finite_places {R Ω : Type} [CommRing R] [IsDomain R] [Field Ω] [CharZero Ω] [Algebra R Ω]
    [Algebra (FractionRing R) Ω] [IsScalarTower R (FractionRing R) Ω]
    [FiniteDimensional (FractionRing R) Ω]
    (P : Ideal R) [P.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime P)] :
    {v : AddValuation Ω (WithTop ℤ) | IsNormDiscrete v ∧
      ∀ x : R, 0 ≤ v (algebraMap R Ω x) ∧ (0 < v (algebraMap R Ω x) ↔ x ∈ P)}.Finite := by sorry
