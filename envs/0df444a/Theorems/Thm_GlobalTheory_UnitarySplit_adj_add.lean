-- Prove2me | Theorems.Thm_GlobalTheory_UnitarySplit_adj_add
-- name    : GlobalTheory.UnitarySplit.adj_add
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:47:03.30625+00:00
-- url     : https://prove2.me/theorems/0472ea5a-26c6-4524-8ed2-1ea6234cfd94
-- title:
--   Unitary Split: adj add
-- statement:
--   The Unitary Split construction uses the adj add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UnitarySupportedEquiv.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UnitarySupportedEquiv.lean#L25-L27

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

theorem GlobalTheory.UnitarySplit.adj_add (c : A →+* A) (J M N : Matrix (Fin n) (Fin n) A) :
    adj c J (M + N) = adj c J M + adj c J N := by sorry
