-- Prove2me | Theorems.Thm_GlobalTheory_VerticalGauss_nonneg_of_isIntegral
-- name    : GlobalTheory.VerticalGauss.nonneg_of_isIntegral
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:13:54.746123+00:00
-- url     : https://prove2.me/theorems/96557449-3b08-432a-a6a4-44f3f91c7e30
-- title:
--   Vertical Gauss: nonneg of is Integral
-- statement:
--   The Vertical Gauss construction uses the nonneg of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/FiniteVerticalGaussValuations.lean#L108-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/FiniteVerticalGaussValuations.lean#L108-L116

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

theorem GlobalTheory.VerticalGauss.nonneg_of_isIntegral {R Ω : Type} [CommRing R] [Field Ω] [Algebra R Ω]
    (w : AddValuation Ω (WithTop ℤ)) (h : ∀ r, 0 ≤ w (algebraMap R Ω r)) {b : Ω}
    (hb : IsIntegral R b) : 0 ≤ w b := by sorry
