-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_convPow_apply_groupLike
-- name    : GlobalTheory.PDiv.convPow_apply_groupLike
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:38:43.027056+00:00
-- url     : https://prove2.me/theorems/502b5ff4-01a9-43b3-b712-6a8fbb3f5c90
-- title:
--   PDiv: conv Pow apply group Like
-- statement:
--   The PDiv construction uses the conv Pow apply group Like property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L41-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L41-L45

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

theorem GlobalTheory.PDiv.convPow_apply_groupLike (x : WithConv (A →ₐ[R] B)) {u : A} (hu : IsGroupLikeElem R u)
    (n : ℕ) : (x ^ n) u = x u ^ n := by sorry
