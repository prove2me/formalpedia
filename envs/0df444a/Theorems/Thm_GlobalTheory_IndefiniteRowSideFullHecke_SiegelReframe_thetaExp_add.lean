-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SiegelReframe_thetaExp_add
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.thetaExp_add
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:15:43.702464+00:00
-- url     : https://prove2.me/theorems/fc04399b-a6eb-424c-9c8c-a578e49638fb
-- title:
--   Siegel Reframe: theta Exp add
-- statement:
--   The Siegel Reframe construction uses the theta Exp add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/SiegelReframe.lean#L273-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/SiegelReframe.lean#L273-L288

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_SiegelReframe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open scoped Real ContDiff
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe

theorem GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.thetaExp_add {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ.IsSymm) (l l' : Fl g)
    (z : Fin g → ℂ) :
    thetaExp τ (l + l') z = thetaExp τ l (z + per τ l') + thetaExp τ l' z +
      ∑ i, (l (Sum.inl i) : ℂ) * (l' (Sum.inr i) : ℂ) := by sorry
