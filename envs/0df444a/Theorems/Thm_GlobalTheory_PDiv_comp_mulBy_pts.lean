-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_comp_mulBy_pts
-- name    : GlobalTheory.PDiv.comp_mulBy_pts
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:36:58.520566+00:00
-- url     : https://prove2.me/theorems/043779a5-a412-4084-8a5b-8dca8e894387
-- title:
--   PDiv: comp mul By pts
-- statement:
--   The PDiv construction uses the comp mul By pts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L85-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L85-L88

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

theorem GlobalTheory.PDiv.comp_mulBy_pts [IsCocomm R A] {E : Type*} [CommRing E] [Algebra R E] (x : A →ₐ[R] E)
    (n : ℕ) : x.comp (mulBy R A n : A →ₐ[R] A) = (toConv x ^ n).ofConv := by sorry
