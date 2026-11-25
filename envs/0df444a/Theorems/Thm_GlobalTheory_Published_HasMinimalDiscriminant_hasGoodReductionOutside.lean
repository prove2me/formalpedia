-- Prove2me | Theorems.Thm_GlobalTheory_Published_HasMinimalDiscriminant_hasGoodReductionOutside
-- name    : GlobalTheory.Published.HasMinimalDiscriminant.hasGoodReductionOutside
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:16:18.508241+00:00
-- url     : https://prove2.me/theorems/f81120f0-634e-4d5a-93cb-f2543cb88e7f
-- title:
--   Has Minimal Discriminant: has Good Reduction Outside
-- statement:
--   The Has Minimal Discriminant construction uses the has Good Reduction Outside property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/CmCurveGoodOutsidePrimePremises.lean#L185-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/CmCurveGoodOutsidePrimePremises.lean#L185-L200

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_ComplexMultiplicationJPremises
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__CmCurveGoodOutsidePrimePremises_e87ddea43482082e
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain WeierstrassCurve
open scoped nonZeroDivisors IntermediateField
open GlobalTheory GlobalTheory.Published
variable {p : ℕ}

theorem GlobalTheory.Published.HasMinimalDiscriminant.hasGoodReductionOutside {F : Type} [Field F] [NumberField F]
    {A : WeierstrassCurve F} (h : HasMinimalDiscriminant A (-(p : F) ^ 3)) :
    HasGoodReductionOutside p A := by sorry
