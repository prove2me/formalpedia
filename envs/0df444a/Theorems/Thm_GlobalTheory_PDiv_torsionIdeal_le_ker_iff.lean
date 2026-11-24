-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_torsionIdeal_le_ker_iff
-- name    : GlobalTheory.PDiv.torsionIdeal_le_ker_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:38:48.013269+00:00
-- url     : https://prove2.me/theorems/aa70770c-2e86-48a6-91f7-5fce6c27cae4
-- title:
--   PDiv: torsion Ideal le ker iff
-- statement:
--   The PDiv construction uses the torsion Ideal le ker iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L137-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L137-L146

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

theorem GlobalTheory.PDiv.torsionIdeal_le_ker_iff [IsCocomm R A] (n : ℕ) {E : Type*} [CommRing E] [Algebra R E]
    (x : A →ₐ[R] E) : torsionIdeal R A n ≤ RingHom.ker x ↔ toConv x ^ n = 1 := by sorry
