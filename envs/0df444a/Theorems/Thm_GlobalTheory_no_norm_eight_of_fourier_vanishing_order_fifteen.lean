-- Prove2me | Theorems.Thm_GlobalTheory_no_norm_eight_of_fourier_vanishing_order_fifteen
-- name    : GlobalTheory.no_norm_eight_of_fourier_vanishing_order_fifteen
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:12:15.303923+00:00
-- url     : https://prove2.me/theorems/d653a066-b79d-4b23-9da5-e3785d879f66
-- title:
--   Global Theory: no norm eight of fourier vanishing order fifteen
-- statement:
--   The Global Theory construction uses the no norm eight of fourier vanishing order fifteen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/NoNormEightOfFourierVanishingOrderFifteen.lean#L8-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/NoNormEightOfFourierVanishingOrderFifteen.lean#L8-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_NoNormEightOfFourierVanishingOrderFifteen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory

theorem GlobalTheory.no_norm_eight_of_fourier_vanishing_order_fifteen :
    ∀ (ω : ℂ) (c : ℕ → ℤ), IsPrimitiveRoot ω 15 → ∑ k ∈ Finset.range 15, c k ^ 2 = 8 →
      (∀ j : ℕ, j < 15 → ¬ 5 ∣ j → ∑ k ∈ Finset.range 15, (c k : ℂ) * ω ^ (j * k) = 0) → False := by sorry
