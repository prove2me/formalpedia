-- Prove2me | Theorems.Thm_GlobalTheory_KeyKa_graded_inv
-- name    : GlobalTheory.KeyKa.graded_inv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:49:32.679086+00:00
-- url     : https://prove2.me/theorems/719a957a-3709-4928-8141-7bd03cf0cc63
-- title:
--   Key Ka: graded inv
-- statement:
--   The Key Ka construction uses the graded inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SubmatrixMulOfSupport.lean#L7-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SubmatrixMulOfSupport.lean#L7-L29

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

theorem GlobalTheory.KeyKa.graded_inv {R Ix : Type} [CommRing R] [Fintype Ix] [DecidableEq Ix] (deg : Ix → ℕ)
    (G G' : Matrix Ix Ix R) (hG : ∀ p q, deg p ≠ deg q → G p q = 0) (hGG : G * G' = 1) :
    ∀ p q, deg p ≠ deg q → G' p q = 0 := by sorry
