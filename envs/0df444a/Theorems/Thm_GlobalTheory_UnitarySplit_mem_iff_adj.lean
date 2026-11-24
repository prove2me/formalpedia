-- Prove2me | Theorems.Thm_GlobalTheory_UnitarySplit_mem_iff_adj
-- name    : GlobalTheory.UnitarySplit.mem_iff_adj
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:46:13.983953+00:00
-- url     : https://prove2.me/theorems/9a18ca2a-6817-4a24-bc07-896e0d633cda
-- title:
--   Unitary Split: mem iff adj
-- statement:
--   The Unitary Split construction uses the mem iff adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UnitarySupportedEquiv.lean#L52-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UnitarySupportedEquiv.lean#L52-L62

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitarySupportedEquiv
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG
open GlobalTheory GlobalTheory.UnitarySplit
variable {A : Type} [CommRing A] {n : ℕ}

theorem GlobalTheory.UnitarySplit.mem_iff_adj (c : A →+* A) {J : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J.det)
    (G : GL (Fin n) A) :
    G ∈ UJ c J ↔ adj c J (G : Matrix (Fin n) (Fin n) A) * (G : Matrix (Fin n) (Fin n) A) = 1 := by sorry
