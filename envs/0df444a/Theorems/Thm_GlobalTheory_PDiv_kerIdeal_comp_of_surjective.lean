-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_kerIdeal_comp_of_surjective
-- name    : GlobalTheory.PDiv.kerIdeal_comp_of_surjective
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:36:52.163165+00:00
-- url     : https://prove2.me/theorems/f4422f40-ce77-4c56-ac2c-bde6dd70d8cb
-- title:
--   PDiv: ker Ideal comp of surjective
-- statement:
--   The PDiv construction uses the ker Ideal comp of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L159-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L159-L161

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

theorem GlobalTheory.PDiv.kerIdeal_comp_of_surjective (g : A →ₐc[R] B) {f : C →ₐc[R] A}
    (hf : Function.Surjective f) : kerIdeal (g.comp f) = kerIdeal g := by sorry
