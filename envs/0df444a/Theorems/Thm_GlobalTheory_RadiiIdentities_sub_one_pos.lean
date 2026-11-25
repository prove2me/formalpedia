-- Prove2me | Theorems.Thm_GlobalTheory_RadiiIdentities_sub_one_pos
-- name    : GlobalTheory.RadiiIdentities.sub_one_pos
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:24:12.264287+00:00
-- url     : https://prove2.me/theorems/fc19c2ee-1db4-4bbc-9723-e7401401b2cf
-- title:
--   Radii Identities: sub one pos
-- statement:
--   The Radii Identities construction uses the sub one pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/RadiiValuationDifferences.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/RadiiValuationDifferences.lean#L10-L12

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RadiiValuationDifferences
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
open GlobalTheory
open GlobalTheory.RadiiIdentities

theorem GlobalTheory.RadiiIdentities.sub_one_pos {l : ℕ} (hl : 2 ≤ l) : (0 : ℝ) < (l : ℝ) - 1 := by sorry
