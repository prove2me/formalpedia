-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_pow_digit_natCast
-- name    : GlobalTheory.PDiv.pow_digit_natCast
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:36:43.06274+00:00
-- url     : https://prove2.me/theorems/1e550885-6261-4d3e-ac9e-cab4cd727f86
-- title:
--   PDiv: pow digit nat Cast
-- statement:
--   The PDiv construction uses the pow digit nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L371-L372
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L371-L372

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

theorem GlobalTheory.PDiv.pow_digit_natCast {n : ℕ} {x : M} (hx : x ^ p ^ n = 1) (k : ℕ) :
    x ^ digit n (k : ℤ_[p]) = x ^ k := by sorry
