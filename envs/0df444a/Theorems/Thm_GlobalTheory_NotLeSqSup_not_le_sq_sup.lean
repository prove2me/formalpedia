-- Prove2me | Theorems.Thm_GlobalTheory_NotLeSqSup_not_le_sq_sup
-- name    : GlobalTheory.NotLeSqSup.not_le_sq_sup
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:35:56.038029+00:00
-- url     : https://prove2.me/theorems/4f23ee9a-bf30-410d-8792-4bbb0a743344
-- title:
--   Not Le Sq Sup: not le sq sup
-- statement:
--   The Not Le Sq Sup construction uses the not le sq sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NotLeSqSup.lean#L5-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/NotLeSqSup.lean#L5-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NotLeSqSup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NotLeSqSup

theorem GlobalTheory.NotLeSqSup.not_le_sq_sup {A : Type} [CommRing A] {m I : Ideal A} {n : ℕ}
    (hn : m ^ (n + 1) = ⊥) (hI : ¬ m ≤ I) : ¬ m ≤ m ^ 2 ⊔ I := by sorry
