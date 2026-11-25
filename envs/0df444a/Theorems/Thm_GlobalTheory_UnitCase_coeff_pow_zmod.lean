-- Prove2me | Theorems.Thm_GlobalTheory_UnitCase_coeff_pow_zmod
-- name    : GlobalTheory.UnitCase.coeff_pow_zmod
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:36:45.929978+00:00
-- url     : https://prove2.me/theorems/31773aa2-77fb-4bcd-b051-0e69dba6418d
-- title:
--   Unit Case: coeff pow zmod
-- statement:
--   The Unit Case construction uses the coeff pow zmod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L160-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L160-L165

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

theorem GlobalTheory.UnitCase.coeff_pow_zmod {l : ℕ} (hl : l.Prime) (q : MvPolynomial κ ℤ) (A : κ →₀ ℕ) :
    ((MvPolynomial.coeff A (q ^ l) : ℤ) : ZMod l) =
      MvPolynomial.coeff A (MvPolynomial.expand l (MvPolynomial.map (Int.castRingHom (ZMod l)) q)) := by sorry
