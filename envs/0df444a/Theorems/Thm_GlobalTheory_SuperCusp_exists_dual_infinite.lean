-- Prove2me | Theorems.Thm_GlobalTheory_SuperCusp_exists_dual_infinite
-- name    : GlobalTheory.SuperCusp.exists_dual_infinite
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:23:55.448161+00:00
-- url     : https://prove2.me/theorems/c1764b79-f5a2-4038-90cb-a1179806a89a
-- title:
--   Super Cusp: exists dual infinite
-- statement:
--   The Super Cusp construction uses the exists dual infinite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCuspidalOfIsSupercuspidal.lean#L12-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCuspidalOfIsSupercuspidal.lean#L12-L50

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

theorem GlobalTheory.SuperCusp.exists_dual_infinite {Q : Type} [AddCommGroup Q] [Module ℂ Q] (w : ℕ → Q) (hw : ∀ r, w r ≠ 0) :
    ∃ φ : Module.Dual ℂ Q, {r | φ (w r) ≠ 0}.Infinite := by sorry
