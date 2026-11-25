-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_ker_eq_of_fibreDim_eq
-- name    : GlobalTheory.PDiv.ker_eq_of_fibreDim_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:46:41.729198+00:00
-- url     : https://prove2.me/theorems/47d2dca8-f9c2-450d-b36c-b725c7f1cedd
-- title:
--   PDiv: ker eq of fibre Dim eq
-- statement:
--   The PDiv construction uses the ker eq of fibre Dim eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/FibreRankCompOfSurjective.lean#L106-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/FibreRankCompOfSurjective.lean#L106-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_KerIdealCompOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PointsGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSpanEqTopOfFinrankFibreEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerCounitAlgHomBaseChangeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankDualAndRangeDualMapBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubsingletonOfResidueFieldFibres
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module
open GlobalTheory GlobalTheory.PDiv
variable {O : Type} [CommRing O]
variable {A B : Type} [CommRing A] [CommRing B] [HopfAlgebra O A] [HopfAlgebra O B]
  [Module.Finite O A]
variable [Module.Projective O A] [Module.Finite O B] [Module.Projective O B]

theorem GlobalTheory.PDiv.ker_eq_of_fibreDim_eq {D E : Type} [CommRing D] [CommRing E] [Algebra O D] [Algebra O E]
    [Module.Finite O D] [Module.Finite O E] [Module.Projective O E] (π : D →ₐ[O] E)
    (hπ : Function.Surjective π) (I : Ideal D) (hI : I ≤ RingHom.ker π)
    (h : ∀ q : PrimeSpectrum O, fibreDim (D ⧸ I) q = fibreDim E q) : RingHom.ker π = I := by sorry
