-- Prove2me | Theorems.Thm_GlobalTheory_UnitCase_jet_sub_mem
-- name    : GlobalTheory.UnitCase.jet_sub_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:40:55.47284+00:00
-- url     : https://prove2.me/theorems/c86379f8-bf01-4266-a87f-c9bc7bee453e
-- title:
--   Unit Case: jet sub mem
-- statement:
--   The Unit Case construction uses the jet sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L443-L462
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L443-L462

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

theorem GlobalTheory.UnitCase.jet_sub_mem [CharZero C] [Fintype κ] {l : ℕ} (hl : l.Prime) (O : Subring C)
    (hO : ∀ n : ℕ, ¬ l ∣ n → (n : C)⁻¹ ∈ O) (q : MvPolynomial κ ℤ)
    (hB : ∀ B ∈ q.support, ∀ j, B j < l)
    (hAB : ∀ A ∈ (q ^ l).support, ∀ B ∈ q.support, ∑ j, A j = l * ∑ j, B j)
    (G : MvPowerSeries (κ ⊕ κ) C) (hG0 : MvPowerSeries.coeff 0 G = 1)
    (hG : ∀ A ∈ (q ^ l).support, ∀ B ∈ q.support,
      ∀ m ≤ Finsupp.sumElim A B, MvPowerSeries.coeff m G ∈ O) :
    jetAt0 (MvPolynomial.rename Sum.inl (MvPolynomial.map (Int.castRingHom C) (q ^ l)) *
        MvPolynomial.rename Sum.inr (MvPolynomial.map (Int.castRingHom C) q))
        (mvExp (mainTerm l (-(l : C)⁻¹)) * G) -
      ∑ B ∈ q.support, ((MvPolynomial.coeff B q : ℤ) : C) * mfact B *
        (MvPolynomial.coeff B q : ℤ) ∈ mult O l := by sorry
