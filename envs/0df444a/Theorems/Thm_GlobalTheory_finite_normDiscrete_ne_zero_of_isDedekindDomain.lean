-- Prove2me | Theorems.Thm_GlobalTheory_finite_normDiscrete_ne_zero_of_isDedekindDomain
-- name    : GlobalTheory.finite_normDiscrete_ne_zero_of_isDedekindDomain
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:57:55.934015+00:00
-- url     : https://prove2.me/theorems/1776f969-ae20-4e1d-b226-1fe10a009e6b
-- title:
--   Global Theory: finite norm Discrete ne zero of is Dedekind Domain
-- statement:
--   The Global Theory construction uses the finite norm Discrete ne zero of is Dedekind Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/FiniteNormDiscreteNeZeroOfIsDedekindDomain.lean#L11-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/FiniteNormDiscreteNeZeroOfIsDedekindDomain.lean#L11-L57

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_FiniteNormDiscreteNeZeroOfIsDedekindDomain
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

theorem GlobalTheory.finite_normDiscrete_ne_zero_of_isDedekindDomain {S L : Type*} [CommRing S]
    [IsDedekindDomain S] [Field L] [Algebra S L] [IsFractionRing S L] (g : L) (hg : g ≠ 0) :
    {w : AddValuation L (WithTop ℤ) |
      IsNormDiscrete w ∧ (∀ s : S, 0 ≤ w (algebraMap S L s)) ∧ w g ≠ 0}.Finite := by sorry
