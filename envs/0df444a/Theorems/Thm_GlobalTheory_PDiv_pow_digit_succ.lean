-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_pow_digit_succ
-- name    : GlobalTheory.PDiv.pow_digit_succ
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:37:11.957935+00:00
-- url     : https://prove2.me/theorems/20f31813-1c0f-4f98-ac0d-bc5dbe1ffa78
-- title:
--   PDiv: pow digit succ
-- statement:
--   The PDiv construction uses the pow digit succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L389-L393
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L389-L393

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

theorem GlobalTheory.PDiv.pow_digit_succ {n : ℕ} {x : M} (hx : x ^ p ^ n = 1) (a : ℤ_[p]) :
    x ^ digit (n + 1) a = x ^ digit n a := by sorry
