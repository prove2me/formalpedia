-- Prove2me | Theorems.Thm_GlobalTheory_JR_OKCompact_charpoly_smul_eq_scaleRoots
-- name    : GlobalTheory.JR.OKCompact.charpoly_smul_eq_scaleRoots
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:34:20.368728+00:00
-- url     : https://prove2.me/theorems/722cce91-c5aa-482e-8110-4bb16dafdeb1
-- title:
--   OKCompact: charpoly smul eq scale Roots
-- statement:
--   The OKCompact construction uses the charpoly smul eq scale Roots property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCompactFiniteEtaleHermitianPairOK.lean#L21-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCompactFiniteEtaleHermitianPairOK.lean#L21-L31

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

theorem GlobalTheory.JR.OKCompact.charpoly_smul_eq_scaleRoots {K : Type} [Field K] [Infinite K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    {c : K} (hc : c ≠ 0) : (c • M).charpoly = M.charpoly.scaleRoots c := by sorry
