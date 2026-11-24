-- Prove2me | Theorems.Thm_GlobalTheory_SuperCusp_val_mul_le_one
-- name    : GlobalTheory.SuperCusp.val_mul_le_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:23:42.827815+00:00
-- url     : https://prove2.me/theorems/d6d8e255-0f9f-462b-95a2-b21021be57b2
-- title:
--   Super Cusp: val mul le one
-- statement:
--   The Super Cusp construction uses the val mul le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCuspidalOfIsSupercuspidal.lean#L117-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCuspidalOfIsSupercuspidal.lean#L117-L120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CentralExponentBoundOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubsingletonJacquetOfPerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsInvariantForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCuspidalOfIsSupercuspidal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix Topology Filter
noncomputable section
open GlobalTheory GlobalTheory.SuperCusp

theorem GlobalTheory.SuperCusp.val_mul_le_one {k : Type} [Field k] [ValuativeRel k] {n : Type} [Fintype n] {P Q : Matrix n n k}
    (hP : ∀ p q, valuation k (P p q) ≤ 1) (hQ : ∀ p q, valuation k (Q p q) ≤ 1) (p q : n) :
    valuation k ((P * Q) p q) ≤ 1 := by sorry
