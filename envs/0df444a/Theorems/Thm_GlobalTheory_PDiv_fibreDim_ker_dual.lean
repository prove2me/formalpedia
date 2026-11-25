-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_fibreDim_ker_dual
-- name    : GlobalTheory.PDiv.fibreDim_ker_dual
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:46:12.503345+00:00
-- url     : https://prove2.me/theorems/c2a38297-bf07-4334-956c-21fcf3f5b977
-- title:
--   PDiv: fibre Dim ker dual
-- statement:
--   The PDiv construction uses the fibre Dim ker dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/FibreRankCompOfSurjective.lean#L94-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/FibreRankCompOfSurjective.lean#L94-L104

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_KerIdealCompOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PointsGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSpanEqTopOfFinrankFibreEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerCounitAlgHomBaseChangeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankDualAndRangeDualMapBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubsingletonOfResidueFieldFibres
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FibreRankCompOfSurjective
import Theorems.Thm_GlobalTheory_IsBicharacter_map

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

theorem GlobalTheory.PDiv.fibreDim_ker_dual [IsCocomm O A] (g : A →ₐc[O] A) (q : PrimeSpectrum O) :
    fibreDim (CartierDual O A ⧸ kerIdeal (CartierDual.map g)) q =
      fibreDim (A ⧸ kerIdeal g) q := by sorry
