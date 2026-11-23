-- Prove2me | Theorems.Thm_GlobalTheory_PeriodDvd_killed_eq_image
-- name    : GlobalTheory.PeriodDvd.killed_eq_image
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:08.983675+00:00
-- url     : https://prove2.me/theorems/bfcc6e60-e380-456d-ac0a-152d42276674
-- title:
--   Period Dvd: killed eq image
-- statement:
--   The Period Dvd construction uses the killed eq image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DvdOfPeriodOfDvdSumPowersetCard.lean#L16-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DvdOfPeriodOfDvdSumPowersetCard.lean#L16-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardDvdSumOfInvariantOfCardStabilizerDvd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvdOfPeriodOfDvdSumPowersetCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Pointwise
open GlobalTheory
open GlobalTheory.PeriodDvd

theorem GlobalTheory.PeriodDvd.killed_eq_image {d : ℕ} [NeZero d] {s e : ℕ} (h : s * e = d) :
    killed d s = (Finset.range s).image fun j => ((e * j : ℕ) : ZMod d) := by sorry
