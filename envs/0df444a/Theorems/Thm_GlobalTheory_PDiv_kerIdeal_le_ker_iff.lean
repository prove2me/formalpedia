-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_kerIdeal_le_ker_iff
-- name    : GlobalTheory.PDiv.kerIdeal_le_ker_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:37:05.134339+00:00
-- url     : https://prove2.me/theorems/2ccd3ee7-83fd-4c61-b47b-23f2a73b21f4
-- title:
--   PDiv: ker Ideal le ker iff
-- statement:
--   The PDiv construction uses the ker Ideal le ker iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L123-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L123-L135

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

theorem GlobalTheory.PDiv.kerIdeal_le_ker_iff (f : C →ₐc[R] A) {E : Type*} [CommRing E] [Algebra R E]
    (x : A →ₐ[R] E) :
    kerIdeal f ≤ RingHom.ker x ↔ ∀ c, x (f c) = algebraMap R E (counit c) := by sorry
