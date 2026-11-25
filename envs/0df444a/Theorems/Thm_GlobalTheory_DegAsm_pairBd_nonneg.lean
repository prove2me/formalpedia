-- Prove2me | Theorems.Thm_GlobalTheory_DegAsm_pairBd_nonneg
-- name    : GlobalTheory.DegAsm.pairBd_nonneg
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:11:23.211258+00:00
-- url     : https://prove2.me/theorems/413441b0-54c9-5c42-8768-84dd94536088
-- title:
--   Deg Asm: pair Bd nonneg
-- statement:
--   The Deg Asm construction uses the pair Bd nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/PairBdNonneg.lean#L26-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/PairBdNonneg.lean#L26-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_PairBdNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField GlobalTheory.DegCnt
open GlobalTheory GlobalTheory.DegAsm
open NumberField

theorem GlobalTheory.DegAsm.pairBd_nonneg (K : Type) [Field K] [NumberField K]
    (k g j T x x' : ℕ) : 0 ≤ _root_.GlobalTheory.DegAsm.pairBd K k g j T x x' := by sorry
