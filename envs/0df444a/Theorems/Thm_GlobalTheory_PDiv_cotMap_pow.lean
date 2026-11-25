-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_cotMap_pow
-- name    : GlobalTheory.PDiv.cotMap_pow
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:36:51.837941+00:00
-- url     : https://prove2.me/theorems/21cd8724-538b-402e-87fd-903471a41581
-- title:
--   PDiv: cot Map pow
-- statement:
--   The PDiv construction uses the cot Map pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L249-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L249-L253

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

theorem GlobalTheory.PDiv.cotMap_pow [IsCocomm R C] (f : WithConv (C →ₐc[R] A)) (n : ℕ) :
    cotMap (f ^ n).ofConv = n • cotMap f.ofConv := by sorry
