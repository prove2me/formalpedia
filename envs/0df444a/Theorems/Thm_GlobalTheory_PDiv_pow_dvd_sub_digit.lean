-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_pow_dvd_sub_digit
-- name    : GlobalTheory.PDiv.pow_dvd_sub_digit
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:38:11.954496+00:00
-- url     : https://prove2.me/theorems/f2e3d87a-b54a-4fcc-bc95-f25722e28e85
-- title:
--   PDiv: pow dvd sub digit
-- statement:
--   The PDiv construction uses the pow dvd sub digit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L363-L365
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L363-L365

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

theorem GlobalTheory.PDiv.pow_dvd_sub_digit (n : ℕ) (a : ℤ_[p]) : (p : ℤ_[p]) ^ n ∣ a - digit n a := by sorry
