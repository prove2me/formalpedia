-- Prove2me | Theorems.Thm_GlobalTheory_AdicNoeth_isNoetherianRing_of_isAdicComplete
-- name    : GlobalTheory.AdicNoeth.isNoetherianRing_of_isAdicComplete
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:54:28.182328+00:00
-- url     : https://prove2.me/theorems/5f81f518-e835-4d96-b0de-db2fcf1cfa52
-- title:
--   Adic Noeth: is Noetherian Ring of is Adic Complete
-- statement:
--   The Adic Noeth construction uses the is Noetherian Ring of is Adic Complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsNoetherianRingOfIsAdicComplete.lean#L152-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsNoetherianRingOfIsAdicComplete.lean#L152-L161

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGradedRingKernelLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsNoetherianRingOfIsAdicComplete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.AdicNoeth

theorem GlobalTheory.AdicNoeth.isNoetherianRing_of_isAdicComplete : ∀ (R : Type) [CommRing R] (I : Ideal R), I.FG →
    IsAdicComplete I R → IsNoetherianRing (R ⧸ I) → IsNoetherianRing R := by sorry
