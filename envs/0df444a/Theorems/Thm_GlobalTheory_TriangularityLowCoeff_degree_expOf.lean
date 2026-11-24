-- Prove2me | Theorems.Thm_GlobalTheory_TriangularityLowCoeff_degree_expOf
-- name    : GlobalTheory.TriangularityLowCoeff.degree_expOf
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:12:01.091712+00:00
-- url     : https://prove2.me/theorems/21fca7a8-bb37-4501-b678-1f1b2937a35e
-- title:
--   Triangularity Low Coeff: degree exp Of
-- statement:
--   The Triangularity Low Coeff construction uses the degree exp Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffAnnihilatedOfAevalMemKerPow.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffAnnihilatedOfAevalMemKerPow.lean#L25-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffAnnihilatedOfAevalMemKerPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.TriangularityLowCoeff
open MvPolynomial

theorem GlobalTheory.TriangularityLowCoeff.degree_expOf {d : ℕ} (L : List (Fin d)) : (expOf L).degree = L.length := by sorry
