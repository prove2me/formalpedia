-- Prove2me | Theorems.Thm_GlobalTheory_UnitCase_jetAt0_rename_mul
-- name    : GlobalTheory.UnitCase.jetAt0_rename_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:39:39.9502+00:00
-- url     : https://prove2.me/theorems/b7cb5c87-9528-4363-ad38-9ac8d9fc0910
-- title:
--   Unit Case: jet At0 rename mul
-- statement:
--   The Unit Case construction uses the jet At0 rename mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L428-L441
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L428-L441

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

theorem GlobalTheory.UnitCase.jetAt0_rename_mul [Fintype κ] (p q : MvPolynomial κ ℤ) (G : MvPowerSeries (κ ⊕ κ) C) :
    jetAt0 (MvPolynomial.rename Sum.inl (MvPolynomial.map (Int.castRingHom C) p) *
        MvPolynomial.rename Sum.inr (MvPolynomial.map (Int.castRingHom C) q)) G =
      ∑ A ∈ p.support, ∑ B ∈ q.support,
        ((MvPolynomial.coeff A p : ℤ) : C) * (MvPolynomial.coeff B q : ℤ) *
          ((mfact A : C) * mfact B) * MvPowerSeries.coeff (Finsupp.sumElim A B) G := by sorry
