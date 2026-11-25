-- Prove2me | Theorems.Thm_GlobalTheory_exists_pt_ord_eq_addValuation
-- name    : GlobalTheory.exists_pt_ord_eq_addValuation
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:19:40.920125+00:00
-- url     : https://prove2.me/theorems/1d10ead6-32ad-446d-8d48-018491262caf
-- title:
--   Global Theory: exists pt ord eq add Valuation
-- statement:
--   The Global Theory construction uses the exists pt ord eq add Valuation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsPtOrdEqAddValuation.lean#L65-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsPtOrdEqAddValuation.lean#L65-L174

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

theorem GlobalTheory.exists_pt_ord_eq_addValuation : ∀ (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A] (ϖ : O), IsUnif A ϖ → ∀ [∀ ζ : Pts O A, IsDVRAt ζ] (u : AddValuation A (WithTop ℤ)), (∀ a ∈ As O A, 0 ≤ u a) → 0 < u (algebraMap O A ϖ) → (∃ a, u a = 1) → ∃ ζ : Pts O A, ∀ a, ord ϖ ζ a = u a := by sorry
