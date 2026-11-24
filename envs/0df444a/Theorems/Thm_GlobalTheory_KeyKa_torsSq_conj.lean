-- Prove2me | Theorems.Thm_GlobalTheory_KeyKa_torsSq_conj
-- name    : GlobalTheory.KeyKa.torsSq_conj
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:49:34.739798+00:00
-- url     : https://prove2.me/theorems/66fd16df-3318-4b51-9eb2-155b4c1ed060
-- title:
--   Key Ka: tors Sq conj
-- statement:
--   The Key Ka construction uses the tors Sq conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SubmatrixMulOfSupport.lean#L42-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SubmatrixMulOfSupport.lean#L42-L99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubmatrixMulOfSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.KeyKa

theorem GlobalTheory.KeyKa.torsSq_conj : ∀ (R Ix : Type) [CommRing R] [Fintype Ix] [DecidableEq Ix] (deg : Ix → ℕ) (D : Matrix Ix Ix R) (G G' : Matrix Ix Ix R) (t : R), (∀ p q, deg p ≠ deg q → G p q = 0) → G * G' = 1 → IsCx deg D → TorsSq deg D t → ∃ t', TorsSq deg (G' * D * G) t' ∧ t' * (G.submatrix (fun p : {p // Even (deg p)} => p.1) (fun p : {p // Even (deg p)} => p.1)).det ^ 2 = t * (G.submatrix (fun p : {p // ¬ Even (deg p)} => p.1) (fun p : {p // ¬ Even (deg p)} => p.1)).det ^ 2 := by sorry
