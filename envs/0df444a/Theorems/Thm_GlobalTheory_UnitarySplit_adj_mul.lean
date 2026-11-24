-- Prove2me | Theorems.Thm_GlobalTheory_UnitarySplit_adj_mul
-- name    : GlobalTheory.UnitarySplit.adj_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:46:48.895152+00:00
-- url     : https://prove2.me/theorems/29e66aed-9283-4795-9018-29ba110c5a10
-- title:
--   Unitary Split: adj mul
-- statement:
--   The Unitary Split construction uses the adj mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UnitarySupportedEquiv.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UnitarySupportedEquiv.lean#L37-L39

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

theorem GlobalTheory.UnitarySplit.adj_mul (c : A →+* A) {J : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J.det)
    (M N : Matrix (Fin n) (Fin n) A) : adj c J (M * N) = adj c J N * adj c J M := by sorry
