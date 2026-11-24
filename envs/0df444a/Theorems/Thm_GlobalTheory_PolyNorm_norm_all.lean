-- Prove2me | Theorems.Thm_GlobalTheory_PolyNorm_norm_all
-- name    : GlobalTheory.PolyNorm.norm_all
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:50:55.106945+00:00
-- url     : https://prove2.me/theorems/d21454f0-dc0e-4be5-b0b1-5c7fe01ef687
-- title:
--   Poly Norm: norm all
-- statement:
--   The Poly Norm construction uses the norm all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqProdOfMul.lean#L204-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqProdOfMul.lean#L204-L234

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

theorem GlobalTheory.PolyNorm.norm_all {l : ℕ} [hl : Fact l.Prime] {m : ℕ} (U : Matrix (Fin m) (Fin m) ℤ_[l])
    (N : ℤ[X] → ℚ) (Good : ℤ[X] → Prop)
    (hp : ∀ F : ℤ[X], ∃ p : ℚ[X], ∀ t : ℕ, N (F + t) = p.eval (t : ℚ))
    (hG : ∀ F, ∀ᶠ t : ℕ in Filter.atTop, Good (F + t))
    (hn : ∀ F, Good F → ‖((N F : ℚ) : ℚ_[l])‖ = ‖(Polynomial.aeval U F).det‖) (F : ℤ[X]) :
    ‖((N F : ℚ) : ℚ_[l])‖ = ‖(Polynomial.aeval U F).det‖ := by sorry
