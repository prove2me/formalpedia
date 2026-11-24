-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_mu_bialgHom_ext
-- name    : GlobalTheory.PDiv.mu_bialgHom_ext
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:37:11.248807+00:00
-- url     : https://prove2.me/theorems/107603a8-d3b7-4f64-9aee-96d711bfa3ff
-- title:
--   PDiv: mu bialg Hom ext
-- statement:
--   The PDiv construction uses the mu bialg Hom ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L348-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/KerIdealCompOfSurjective.lean#L348-L350

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
variable (R : Type*) [CommRing R] (m : ℕ)
variable {R m} [NeZero m] {B : Type*} [CommRing B] [Algebra R B]

theorem GlobalTheory.PDiv.mu_bialgHom_ext {A : Type*} [CommRing A] [Bialgebra R A]
    {x y : AddMonoidAlgebra R (ZMod m) →ₐc[R] A} (h : x (muT R m) = y (muT R m)) : x = y := by sorry
