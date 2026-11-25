-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_pow_digit_add
-- name    : GlobalTheory.PDiv.pow_digit_add
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:36:48.780803+00:00
-- url     : https://prove2.me/theorems/639c9a48-ec1a-4ab6-a14f-d27b1af4d8a6
-- title:
--   PDiv: pow digit add
-- statement:
--   The PDiv construction uses the pow digit add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L379-L382
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L379-L382

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

theorem GlobalTheory.PDiv.pow_digit_add {n : ℕ} {x : M} (hx : x ^ p ^ n = 1) (a b : ℤ_[p]) :
    x ^ digit n (a + b) = x ^ digit n a * x ^ digit n b := by sorry
