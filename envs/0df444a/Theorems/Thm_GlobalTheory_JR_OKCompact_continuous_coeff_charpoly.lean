-- Prove2me | Theorems.Thm_GlobalTheory_JR_OKCompact_continuous_coeff_charpoly
-- name    : GlobalTheory.JR.OKCompact.continuous_coeff_charpoly
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:34:21.141653+00:00
-- url     : https://prove2.me/theorems/abcd16c5-8c63-4609-941b-b48186b0a000
-- title:
--   OKCompact: continuous coeff charpoly
-- statement:
--   The OKCompact construction uses the continuous coeff charpoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCompactFiniteEtaleHermitianPairOK.lean#L10-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCompactFiniteEtaleHermitianPairOK.lean#L10-L19

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

theorem GlobalTheory.JR.OKCompact.continuous_coeff_charpoly {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] {n : ℕ}
    (k : ℕ) : Continuous fun M : Matrix (Fin n) (Fin n) A => M.charpoly.coeff k := by sorry
