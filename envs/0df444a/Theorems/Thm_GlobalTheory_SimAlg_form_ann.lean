-- Prove2me | Theorems.Thm_GlobalTheory_SimAlg_form_ann
-- name    : GlobalTheory.SimAlg.form_ann
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:12:38.197575+00:00
-- url     : https://prove2.me/theorems/50ccb87f-c713-4711-83a1-22b6481348ba
-- title:
--   Sim Alg: form ann
-- statement:
--   The Sim Alg construction uses the form ann property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SimilitudeDefiniteFormIsAlgebraicOnVector.lean#L197-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SimilitudeDefiniteFormIsAlgebraicOnVector.lean#L197-L211

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

theorem GlobalTheory.SimAlg.form_ann {Λ : Type} [AddCommGroup Λ] (b : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ)
    (φ : Module.End ℤ Λ) (e : Λ) (P : ℤ[X]) (hP : aeval φ P e = 0) (h : ℂ[X]) :
    form (fun i j => b ((φ ^ i) e) ((φ ^ j) e)) (P.map (Int.castRingHom ℂ)) h = 0 := by sorry
