-- Prove2me | Theorems.Thm_GlobalTheory_UnitarySplit_adj_one
-- name    : GlobalTheory.UnitarySplit.adj_one
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:47:46.005534+00:00
-- url     : https://prove2.me/theorems/16c34eb5-bf90-4665-a269-54f0971f442e
-- title:
--   Unitary Split: adj one
-- statement:
--   The Unitary Split construction uses the adj one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UnitarySupportedEquiv.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UnitarySupportedEquiv.lean#L33-L35

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

theorem GlobalTheory.UnitarySplit.adj_one (c : A →+* A) {J : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J.det) :
    adj c J 1 = 1 := by sorry
