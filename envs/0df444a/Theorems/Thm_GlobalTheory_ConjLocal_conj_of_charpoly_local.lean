-- Prove2me | Theorems.Thm_GlobalTheory_ConjLocal_conj_of_charpoly_local
-- name    : GlobalTheory.ConjLocal.conj_of_charpoly_local
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:25:10.580797+00:00
-- url     : https://prove2.me/theorems/95ad292f-f421-401c-b6d1-160ac1345fbd
-- title:
--   Conj Local: conj of charpoly local
-- statement:
--   The Conj Local construction uses the conj of charpoly local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConjOfCharpolyLocal.lean#L8-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConjOfCharpolyLocal.lean#L8-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLinearIndependentIterates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConjOfCharpolyLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open GlobalTheory GlobalTheory.ConjLocal

theorem GlobalTheory.ConjLocal.conj_of_charpoly_local : ∀ (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) (Y Y' : Matrix (Fin n) (Fin n) R),
    Y.charpoly = Y'.charpoly → Y.charpoly.Separable →
    ∃ g : GL (Fin n) R, Y' = (g⁻¹ : GL (Fin n) R).val * Y * g.val := by sorry
