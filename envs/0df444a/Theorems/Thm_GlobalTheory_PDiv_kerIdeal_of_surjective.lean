-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_kerIdeal_of_surjective
-- name    : GlobalTheory.PDiv.kerIdeal_of_surjective
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:36:54.923799+00:00
-- url     : https://prove2.me/theorems/225b16f6-3ac1-4225-8ef8-854a9a44ca4c
-- title:
--   PDiv: ker Ideal of surjective
-- statement:
--   The PDiv construction uses the ker Ideal of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L148-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L148-L153

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

theorem GlobalTheory.PDiv.kerIdeal_of_surjective {f : C →ₐc[R] A} (hf : Function.Surjective f) :
    kerIdeal f = augIdeal R A := by sorry
