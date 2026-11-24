-- Prove2me | Theorems.Thm_GlobalTheory_SimAlg_form_shift
-- name    : GlobalTheory.SimAlg.form_shift
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:12:35.803197+00:00
-- url     : https://prove2.me/theorems/a272b8b7-7565-4958-b986-d9a6a2b90fd9
-- title:
--   Sim Alg: form shift
-- statement:
--   The Sim Alg construction uses the form shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SimilitudeDefiniteFormIsAlgebraicOnVector.lean#L178-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SimilitudeDefiniteFormIsAlgebraicOnVector.lean#L178-L188

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

theorem GlobalTheory.SimAlg.form_shift (g : ℕ → ℕ → ℤ) (q : ℤ) (hg : ∀ i j, g (i + 1) (j + 1) = q * g i j)
    (f h : ℂ[X]) : form g (X * f) (X * h) = q * form g f h := by sorry
