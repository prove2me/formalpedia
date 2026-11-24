-- Prove2me | Theorems.Thm_GlobalTheory_DoubleCosetEuler_finsum_pi_prod_eq_prod_finsum
-- name    : GlobalTheory.DoubleCosetEuler.finsum_pi_prod_eq_prod_finsum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:50:14.021484+00:00
-- url     : https://prove2.me/theorems/f1f71b47-2432-48a6-a1d9-be69e1230a5e
-- title:
--   Double Coset Euler: finsum pi prod eq prod finsum
-- statement:
--   The Double Coset Euler construction uses the finsum pi prod eq prod finsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumDoubleCosetEqFinprodLocalSums.lean#L22-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumDoubleCosetEqFinprodLocalSums.lean#L22-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumDoubleCosetEqFinprodLocalSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter
open scoped Classical
open GlobalTheory GlobalTheory.DoubleCosetEuler

theorem GlobalTheory.DoubleCosetEuler.finsum_pi_prod_eq_prod_finsum (J : Type) [Fintype J] (α : J → Type) (f : ∀ j, α j → ℂ)
    (hf : ∀ j, (Function.support (f j)).Finite) :
    ∑ᶠ y : (∀ j, α j), ∏ j, f j (y j) = ∏ j, ∑ᶠ a, f j a := by sorry
