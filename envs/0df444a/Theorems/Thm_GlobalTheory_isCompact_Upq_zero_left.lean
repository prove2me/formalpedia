-- Prove2me | Theorems.Thm_GlobalTheory_isCompact_Upq_zero_left
-- name    : GlobalTheory.isCompact_Upq_zero_left
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:58:04.916702+00:00
-- url     : https://prove2.me/theorems/6a80b899-3027-482d-ab57-368dad74552b
-- title:
--   Global Theory: is Compact Upq zero left
-- statement:
--   The Global Theory construction uses the is Compact Upq zero left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UpqDefiniteCompact.lean#L17-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UpqDefiniteCompact.lean#L17-L26

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UpqDefiniteCompact
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
open GlobalTheory

theorem GlobalTheory.isCompact_Upq_zero_left (q : ℕ) :
    IsCompact (Formalism.UG.Upq 0 q : Set (GL (Fin 0 ⊕ Fin q) ℂ)) := by sorry
