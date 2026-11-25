-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_torsionIdeal_le_of_dvd
-- name    : GlobalTheory.PDiv.torsionIdeal_le_of_dvd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:38:48.565845+00:00
-- url     : https://prove2.me/theorems/3c50f2c5-bc26-4750-abc2-0bab5b474d0c
-- title:
--   PDiv: torsion Ideal le of dvd
-- statement:
--   The PDiv construction uses the torsion Ideal le of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L168-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L168-L175

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
variable {R A B C D : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
variable [Bialgebra R A] [Bialgebra R B] [Bialgebra R C] [Bialgebra R D]

theorem GlobalTheory.PDiv.torsionIdeal_le_of_dvd [IsCocomm R A] {m n : ℕ} (h : m ∣ n) :
    torsionIdeal R A n ≤ torsionIdeal R A m := by sorry
