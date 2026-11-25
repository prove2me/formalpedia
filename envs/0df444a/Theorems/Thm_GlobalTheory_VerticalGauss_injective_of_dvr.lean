-- Prove2me | Theorems.Thm_GlobalTheory_VerticalGauss_injective_of_dvr
-- name    : GlobalTheory.VerticalGauss.injective_of_dvr
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:44:01.781037+00:00
-- url     : https://prove2.me/theorems/695fcba7-9855-4c1d-88c6-3a4553ce46c4
-- title:
--   Vertical Gauss: injective of dvr
-- statement:
--   The Vertical Gauss construction uses the injective of dvr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/FiniteVerticalGaussValuations.lean#L81-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/FiniteVerticalGaussValuations.lean#L81-L106

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

theorem GlobalTheory.VerticalGauss.injective_of_dvr {R Ω : Type} [CommRing R] [IsDomain R] [Field Ω] (φ : R →+* Ω)
    (P : Ideal R) [P.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime P)]
    (hker : ∀ r, φ r = 0 → r ∈ P) (a : R) (ha : a ∈ P) (ha0 : φ a ≠ 0) :
    Function.Injective φ := by sorry
