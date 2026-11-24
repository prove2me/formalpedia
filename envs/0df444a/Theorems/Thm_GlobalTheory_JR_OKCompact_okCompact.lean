-- Prove2me | Theorems.Thm_GlobalTheory_JR_OKCompact_okCompact
-- name    : GlobalTheory.JR.OKCompact.okCompact
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:35:07.873733+00:00
-- url     : https://prove2.me/theorems/398981ca-1864-4ab7-bda7-0135e96b3eb9
-- title:
--   OKCompact: ok Compact
-- statement:
--   The OKCompact construction uses the ok Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCompactFiniteEtaleHermitianPairOK.lean#L63-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCompactFiniteEtaleHermitianPairOK.lean#L63-L162

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCompactFiniteEtaleHermitianPairOK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.OKCompact

theorem GlobalTheory.JR.OKCompact.okCompact : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E), IsCompact A.OK := by sorry
