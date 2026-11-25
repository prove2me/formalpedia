-- Prove2me | Theorems.Thm_GlobalTheory_Per_integers_completeDVR
-- name    : GlobalTheory.Per.integers_completeDVR
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:13:07.747933+00:00
-- url     : https://prove2.me/theorems/673138b9-040e-5923-89d4-846aa3423fb2
-- title:
--   Per: integers complete DVR
-- statement:
--   The Per construction uses the integers complete DVR property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegersCompleteDVR.lean#L156-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegersCompleteDVR.lean#L156-L205

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_BoundedOnFramesIffIntegralOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersCompleteDVR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Per
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

theorem GlobalTheory.Per.integers_completeDVR : ∀ (l : ℕ) [Fact l.Prime], ∀ LL : FinExt l,
    ∃ _ : IsDiscreteValuationRing ↥(OL LL),
      IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) ∧ ((l : ℕ) : ↥(OL LL)) ≠ 0 ∧
      ¬ IsUnit ((l : ℕ) : ↥(OL LL)) ∧ Module.Free ℤ_[l] ↥(OL LL) ∧ Module.Finite ℤ_[l] ↥(OL LL) ∧
      IsFractionRing ↥(OL LL) ↥LL.1 := by sorry
