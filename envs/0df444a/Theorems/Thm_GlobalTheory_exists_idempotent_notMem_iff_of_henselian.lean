-- Prove2me | Theorems.Thm_GlobalTheory_exists_idempotent_notMem_iff_of_henselian
-- name    : GlobalTheory.exists_idempotent_notMem_iff_of_henselian
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:27:20.281128+00:00
-- url     : https://prove2.me/theorems/4dc08133-4ac8-4b7e-9ad9-b4fc6905734c
-- title:
--   Global Theory: exists idempotent not Mem iff of henselian
-- statement:
--   The Global Theory construction uses the exists idempotent not Mem iff of henselian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L119-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L119-L153

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open IsLocalRing Polynomial TensorProduct

theorem GlobalTheory.exists_idempotent_notMem_iff_of_henselian (R : Type*) {S : Type*} [CommRing R]
    [HenselianLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (q : Ideal S) [hq : q.IsMaximal] :
    ∃ e : S, IsIdempotentElem e ∧ ∀ n : Ideal S, n.IsMaximal → (e ∉ n ↔ n = q) := by sorry
