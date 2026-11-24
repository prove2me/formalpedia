-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_dUnit_mul_groupLike
-- name    : GlobalTheory.PDiv.dUnit_mul_groupLike
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:38:10.916811+00:00
-- url     : https://prove2.me/theorems/6b75df02-3f15-4713-9f76-d9074ed946e5
-- title:
--   PDiv: d Unit mul group Like
-- statement:
--   The PDiv construction uses the d Unit mul group Like property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L255-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L255-L258

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

theorem GlobalTheory.PDiv.dUnit_mul_groupLike {u v : A} (hu : IsGroupLikeElem R u) (hv : IsGroupLikeElem R v) :
    dUnit R (u * v) = dUnit R u + dUnit R v := by sorry
