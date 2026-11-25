-- Prove2me | Theorems.Thm_GlobalTheory_valCentreOn_isPrime
-- name    : GlobalTheory.valCentreOn_isPrime
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:18:51.350992+00:00
-- url     : https://prove2.me/theorems/8024f804-22f6-5dca-be61-0044c365caaa
-- title:
--   Global Theory: val Centre On is Prime
-- statement:
--   The Global Theory construction uses the val Centre On is Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsPtOrdEqAddValuation.lean#L30-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsPtOrdEqAddValuation.lean#L30-L41

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAE
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsPtOrdEqAddValuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.T0 Formalism.MainNotions.Gaps.EtaleWeightGaps
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.valCentreOn_isPrime {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    (S : Subalgebra O A) (u : AddValuation A (WithTop ℤ)) (h0 : ∀ a ∈ S, 0 ≤ u a) :
    (valCentreOn S u h0).IsPrime := by sorry
