-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_cast_digit
-- name    : GlobalTheory.PDiv.cast_digit
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:38:47.48282+00:00
-- url     : https://prove2.me/theorems/101d4df1-eaa1-4733-9f4a-ded8e6b0d764
-- title:
--   PDiv: cast digit
-- statement:
--   The PDiv construction uses the cast digit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L360-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L360-L361

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

theorem GlobalTheory.PDiv.cast_digit (n : ℕ) (a : ℤ_[p]) :
    (digit n a : ZMod (p ^ n)) = PadicInt.toZModPow n a := by sorry
