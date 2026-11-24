-- Prove2me | Theorems.Thm_GlobalTheory_JR_charpoly_companion
-- name    : GlobalTheory.JR.charpoly_companion
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:39:34.319924+00:00
-- url     : https://prove2.me/theorems/981dcdfc-a968-4e60-bcda-6bb54c312b0d
-- title:
--   JR: charpoly companion
-- statement:
--   The JR construction uses the charpoly companion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsEtaleHermitianPairIsGenCompanion.lean#L11-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsEtaleHermitianPairIsGenCompanion.lean#L11-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LocallyCompactModuleTopology
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsEtaleHermitianPairIsGenCompanion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR

theorem GlobalTheory.JR.charpoly_companion {k : Type} [Field k] {r : ℕ} (p : Fin r → k) :
    (companion p).charpoly = X ^ r + ∑ i, C (p i) * X ^ (i : ℕ) := by sorry
