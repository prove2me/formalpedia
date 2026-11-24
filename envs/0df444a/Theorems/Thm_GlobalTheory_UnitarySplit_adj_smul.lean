-- Prove2me | Theorems.Thm_GlobalTheory_UnitarySplit_adj_smul
-- name    : GlobalTheory.UnitarySplit.adj_smul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:46:23.726524+00:00
-- url     : https://prove2.me/theorems/55aeca66-8838-460b-93fe-d03705f1dea7
-- title:
--   Unitary Split: adj smul
-- statement:
--   The Unitary Split construction uses the adj smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UnitarySupportedEquiv.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UnitarySupportedEquiv.lean#L29-L31

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

theorem GlobalTheory.UnitarySplit.adj_smul (c : A →+* A) (a : A) (J M : Matrix (Fin n) (Fin n) A) :
    adj c J (a • M) = c a • adj c J M := by sorry
