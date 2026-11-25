-- Prove2me | Theorems.Thm_GlobalTheory_UnitCase_offDiag_mem
-- name    : GlobalTheory.UnitCase.offDiag_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:40:01.018612+00:00
-- url     : https://prove2.me/theorems/68713503-10c8-4512-96c6-43786ac78e24
-- title:
--   Unit Case: off Diag mem
-- statement:
--   The Unit Case construction uses the off Diag mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L296-L352
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L296-L352

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds ReciprocityTheory.PGsh
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.UnitCase
variable {C : Type} [Field C] {σ κ : Type}

theorem GlobalTheory.UnitCase.offDiag_mem [CharZero C] [Fintype κ] {l : ℕ} (hl : l.Prime) (O : Subring C)
    (hO : ∀ n : ℕ, ¬ l ∣ n → (n : C)⁻¹ ∈ O) (q : MvPolynomial κ ℤ) (t : ℤ) (A B : κ →₀ ℕ)
    (hB : ∀ j, B j < l) (hAB : ∑ j, A j = l * ∑ j, B j) (G : MvPowerSeries (κ ⊕ κ) C)
    (hG0 : MvPowerSeries.coeff 0 G = 1)
    (hG : ∀ m ≤ Finsupp.sumElim A B, MvPowerSeries.coeff m G ∈ O) :
    ((MvPolynomial.coeff A (q ^ l) : ℤ) : C) * t * ((mfact A : C) * mfact B) *
        MvPowerSeries.coeff (Finsupp.sumElim A B) (mvExp (mainTerm l (-(l : C)⁻¹)) * G) -
      ((MvPolynomial.coeff A (q ^ l) : ℤ) : C) * t * ((mfact A : C) * mfact B) *
        MvPowerSeries.coeff (Finsupp.sumElim A B) (mvExp (mainTerm l (-(l : C)⁻¹))) ∈
      mult O l := by sorry
