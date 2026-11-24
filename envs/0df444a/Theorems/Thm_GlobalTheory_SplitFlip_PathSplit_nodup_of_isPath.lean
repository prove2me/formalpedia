-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_PathSplit_nodup_of_isPath
-- name    : GlobalTheory.SplitFlip.PathSplit.nodup_of_isPath
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:19:56.605871+00:00
-- url     : https://prove2.me/theorems/afb56687-530e-4686-a095-975751f32cc5
-- title:
--   Path Split: nodup of is Path
-- statement:
--   The Path Split construction uses the nodup of is Path property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlipGridPathAtSquareSplit.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FlipGridPathAtSquareSplit.lean#L26-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlipGridPathAtSquareSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SplitFlip GlobalTheory.SplitFlip.PathSplit
open GlobalTheory.SplitFlip

theorem GlobalTheory.SplitFlip.PathSplit.nodup_of_isPath {γ : List Edge} (h : IsPath γ) : γ.Nodup := by sorry
