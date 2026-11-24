-- Prove2me | Theorems.Thm_GlobalTheory_PolyNorm_ev_homog
-- name    : GlobalTheory.PolyNorm.ev_homog
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:50:44.753844+00:00
-- url     : https://prove2.me/theorems/ea8da24f-3a24-4308-a5f1-5428a8f14062
-- title:
--   Poly Norm: ev homog
-- statement:
--   The Poly Norm construction uses the ev homog property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqProdOfMul.lean#L38-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqProdOfMul.lean#L38-L50

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

theorem GlobalTheory.PolyNorm.ev_homog {r m : ℕ} {Φ : MvPolynomial (Fin r) ℚ} (h : Φ.IsHomogeneous m)
    {K : Type} [CommRing K] [Algebra ℚ K] (c : K) (F : K[X]) :
    ev Φ (C c * F) = c ^ m * ev Φ F := by sorry
