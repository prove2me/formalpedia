-- Prove2me | Theorems.Thm_GlobalTheory_OrderBasis_exists_common
-- name    : GlobalTheory.OrderBasis.exists_common
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:49:16.13727+00:00
-- url     : https://prove2.me/theorems/a6e7a071-517d-58ae-972b-05974e3d91ca
-- title:
--   Order Basis: exists common
-- statement:
--   The Order Basis construction uses the exists common property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsBasisFgMaximalOrderSpanningFree.lean#L112-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsBasisFgMaximalOrderSpanningFree.lean#L112-L118

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsBasisFgMaximalOrderSpanningFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.OrderBasis

theorem GlobalTheory.OrderBasis.exists_common {E : Type} [CommRing E] (R : Subring E) {ι : Type} [Fintype ι]
    (P : ι → E → Prop) (hP : ∀ i d c, c ∈ R → P i d → P i (c * d))
    (h : ∀ i, ∃ d ∈ R, IsUnit d ∧ P i d) : ∃ d ∈ R, IsUnit d ∧ ∀ i, P i d := by sorry
