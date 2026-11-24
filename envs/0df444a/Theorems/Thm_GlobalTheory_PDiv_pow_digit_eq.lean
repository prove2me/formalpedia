-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_pow_digit_eq
-- name    : GlobalTheory.PDiv.pow_digit_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:36:55.915475+00:00
-- url     : https://prove2.me/theorems/2ded59ce-4776-4ebf-929a-04c607064681
-- title:
--   PDiv: pow digit eq
-- statement:
--   The PDiv construction uses the pow digit eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L367-L369
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L367-L369

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MemPrimitiveTensorsIffIsPrimitiveElem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_KerIdealCompOfSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv
open GlobalTheory GlobalTheory.PDiv
variable {p : ℕ} [Fact p.Prime] {M : Type*} [Monoid M]

theorem GlobalTheory.PDiv.pow_digit_eq {n : ℕ} {x : M} (hx : x ^ p ^ n = 1) {a : ℤ_[p]} {k : ℕ}
    (h : (k : ZMod (p ^ n)) = PadicInt.toZModPow n a) : x ^ digit n a = x ^ k := by sorry
