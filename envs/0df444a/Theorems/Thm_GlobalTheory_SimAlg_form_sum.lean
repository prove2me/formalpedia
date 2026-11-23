-- Prove2me | Theorems.Thm_GlobalTheory_SimAlg_form_sum
-- name    : GlobalTheory.SimAlg.form_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:54:33.782446+00:00
-- url     : https://prove2.me/theorems/3dd7e50e-5c8e-44e9-bac8-5130dc0dabe9
-- title:
--   Sim Alg: form sum
-- statement:
--   The Sim Alg construction uses the form sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SimilitudeDefiniteFormIsAlgebraicOnVector.lean#L170-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SimilitudeDefiniteFormIsAlgebraicOnVector.lean#L170-L176

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

theorem GlobalTheory.SimAlg.form_sum (g : ℕ → ℕ → ℤ) (d : ℕ) (f h : ℂ[X]) (hf : f.natDegree < d) (hh : h.natDegree < d) :
    form g f h = ∑ i : Fin d, ∑ j : Fin d, f.coeff i * h.coeff j * (g i j : ℂ) := by sorry
