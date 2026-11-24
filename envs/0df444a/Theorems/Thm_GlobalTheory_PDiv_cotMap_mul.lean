-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_cotMap_mul
-- name    : GlobalTheory.PDiv.cotMap_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:39:01.546682+00:00
-- url     : https://prove2.me/theorems/4dbe7c83-4f23-4972-aa69-619b93da436d
-- title:
--   PDiv: cot Map mul
-- statement:
--   The PDiv construction uses the cot Map mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L231-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L231-L247

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

theorem GlobalTheory.PDiv.cotMap_mul [IsCocomm R C] (f g : WithConv (C →ₐc[R] A)) :
    cotMap (f * g).ofConv = cotMap f.ofConv + cotMap g.ofConv := by sorry
