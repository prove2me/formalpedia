-- Prove2me | Theorems.Thm_GlobalTheory_SimAlg_form_pow
-- name    : GlobalTheory.SimAlg.form_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:51:57.315684+00:00
-- url     : https://prove2.me/theorems/7ca6cd2f-213e-4f23-b695-86e7aed287fb
-- title:
--   Sim Alg: form pow
-- statement:
--   The Sim Alg construction uses the form pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SimilitudeDefiniteFormIsAlgebraicOnVector.lean#L165-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SimilitudeDefiniteFormIsAlgebraicOnVector.lean#L165-L168

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SimilitudeDefiniteFormIsAlgebraicOnVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open GlobalTheory GlobalTheory.SimAlg

theorem GlobalTheory.SimAlg.form_pow (g : ℕ → ℕ → ℤ) (i j : ℕ) : form g (X ^ i) (X ^ j) = g i j := by sorry
