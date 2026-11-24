-- Prove2me | Theorems.Thm_GlobalTheory_PolyNorm_monic_ev
-- name    : GlobalTheory.PolyNorm.monic_ev
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:50:43.884802+00:00
-- url     : https://prove2.me/theorems/a19625a7-7c37-4907-853b-8242ef5e57c7
-- title:
--   Poly Norm: monic ev
-- statement:
--   The Poly Norm construction uses the monic ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqProdOfMul.lean#L153-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqProdOfMul.lean#L153-L183

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqProdOfMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.PolyNorm

theorem GlobalTheory.PolyNorm.monic_ev {m : ℕ} {Φ : MvPolynomial (Fin 2) ℚ} (h : Φ.IsHomogeneous m)
    (h1 : ev Φ (1 : ℚ[X]) = 1) :
    (ev Φ (C X - X : ℚ[X][X])).Monic ∧ (ev Φ (C X - X : ℚ[X][X])).natDegree = m := by sorry
