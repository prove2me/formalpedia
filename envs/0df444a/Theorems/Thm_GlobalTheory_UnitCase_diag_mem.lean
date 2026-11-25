-- Prove2me | Theorems.Thm_GlobalTheory_UnitCase_diag_mem
-- name    : GlobalTheory.UnitCase.diag_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:40:38.014803+00:00
-- url     : https://prove2.me/theorems/2c7858c0-2bd7-46ad-a49e-89dcf989471e
-- title:
--   Unit Case: diag mem
-- statement:
--   The Unit Case construction uses the diag mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L354-L395
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L354-L395

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

theorem GlobalTheory.UnitCase.diag_mem [CharZero C] [Fintype κ] {l : ℕ} (hl : l.Prime) (O : Subring C)
    (q : MvPolynomial κ ℤ) (B : κ →₀ ℕ) :
    (∑ A ∈ (q ^ l).support, ((MvPolynomial.coeff A (q ^ l) : ℤ) : C) *
        (MvPolynomial.coeff B q : ℤ) * ((mfact A : C) * mfact B) *
        MvPowerSeries.coeff (Finsupp.sumElim A B) (mvExp (mainTerm l (-(l : C)⁻¹)))) -
      ((MvPolynomial.coeff B q : ℤ) : C) * mfact B * (MvPolynomial.coeff B q : ℤ) ∈ mult O l := by sorry
