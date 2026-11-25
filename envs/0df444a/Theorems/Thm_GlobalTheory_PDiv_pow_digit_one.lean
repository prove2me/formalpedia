-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_pow_digit_one
-- name    : GlobalTheory.PDiv.pow_digit_one
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:39:12.202802+00:00
-- url     : https://prove2.me/theorems/bb7f62ad-5cdf-462e-9f44-1d5a5bdcbadd
-- title:
--   PDiv: pow digit one
-- statement:
--   The PDiv construction uses the pow digit one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L374-L375
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L374-L375

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

theorem GlobalTheory.PDiv.pow_digit_one {n : ℕ} {x : M} (hx : x ^ p ^ n = 1) : x ^ digit n (1 : ℤ_[p]) = x := by sorry
