-- Prove2me | Theorems.Thm_GlobalTheory_Glue_GalTr_coeff_sl_gal
-- name    : GlobalTheory.Glue.GalTr.coeff_sl_gal
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:06:43.286749+00:00
-- url     : https://prove2.me/theorems/8a9b884a-c8d8-49c3-b6ee-f4cc484c5f22
-- title:
--   Gal Tr: coeff sl gal
-- statement:
--   The Gal Tr construction uses the coeff sl gal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ApplyEqOfMemAdjoin.lean#L149-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ApplyEqOfMemAdjoin.lean#L149-L155

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_EeProd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ApplyEqOfMemAdjoin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped MatrixGroups
open GlobalTheory GlobalTheory.Glue
open GlobalTheory.KZ GlobalTheory.K5
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}
variable {p : ℕ} [Fact p.Prime] {Ωl : Type} [Field Ωl] [Algebra (O0 p) Ωl]
variable {X : GlobalTheory.KZ.Tower Ω ε} {A : ValuationSubring Ω} {T : GlobalTheory.K5.Tower p Ωl} {j : Ω →+* Ωl} {n : ℕ} {ψ : O0 p →+* Ωl}
  {io : KT X (p ^ n) →+* Ωl}

theorem GlobalTheory.Glue.GalTr.coeff_sl_gal (X : GlobalTheory.KZ.Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (b : ℕ) (y : X.K) (r : ℚ) :
    (X.exp (X.sl (ofSL (ModularGroup.T ^ b)) (X.gal s y))).coeff r = eOm ε (r * b) * s ((X.exp y).coeff r) := by sorry
