-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_convMul_apply_groupLike
-- name    : GlobalTheory.PDiv.convMul_apply_groupLike
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:36:31.987809+00:00
-- url     : https://prove2.me/theorems/b7c95955-f635-42f0-bf96-10e6dc2569dd
-- title:
--   PDiv: conv Mul apply group Like
-- statement:
--   The PDiv construction uses the conv Mul apply group Like property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L37-L39

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
variable [Bialgebra R A] [Bialgebra R C] [Algebra R B] [Algebra R D]

theorem GlobalTheory.PDiv.convMul_apply_groupLike (x y : WithConv (A →ₐ[R] B)) {u : A} (hu : IsGroupLikeElem R u) :
    (x * y) u = x u * y u := by sorry
