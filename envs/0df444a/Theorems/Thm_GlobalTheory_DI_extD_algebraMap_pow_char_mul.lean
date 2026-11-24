-- Prove2me | Theorems.Thm_GlobalTheory_DI_extD_algebraMap_pow_char_mul
-- name    : GlobalTheory.DI.extD_algebraMap_pow_char_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:35:43.095387+00:00
-- url     : https://prove2.me/theorems/134a6086-740d-4378-a4ad-42b37982c71f
-- title:
--   DI: ext D algebra Map pow char mul
-- statement:
--   The DI construction uses the ext D algebra Map pow char mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExtDAlgebraMapPowCharMul.lean#L29-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExtDAlgebraMapPowCharMul.lean#L29-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExtDAlgebraMapPowCharMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
variable {K : Type} [CommRing K]
variable (p : ℕ) [Fact p.Prime] [CharP K p]

theorem GlobalTheory.DI.extD_algebraMap_pow_char_mul {d : ExteriorAlgebra K Ω[K⁄ℤ] →+ ExteriorAlgebra K Ω[K⁄ℤ]} (hd : IsExtD ℤ K d)
    (c : K) (x : ExteriorAlgebra K Ω[K⁄ℤ]) :
    d (algebraMap K _ (c ^ p) * x) = algebraMap K _ (c ^ p) * d x := by sorry
