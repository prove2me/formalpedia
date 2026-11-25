-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_fibreRank_comp_of_surjective
-- name    : GlobalTheory.PDiv.fibreRank_comp_of_surjective
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:46:18.229109+00:00
-- url     : https://prove2.me/theorems/e627f197-875c-4a91-a73c-be7e3e715b52
-- title:
--   PDiv: fibre Rank comp of surjective
-- statement:
--   The PDiv construction uses the fibre Rank comp of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/FibreRankCompOfSurjective.lean#L40-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/FibreRankCompOfSurjective.lean#L40-L44

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
variable {M N P : Type} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
  [AddCommGroup P] [Module O P]

theorem GlobalTheory.PDiv.fibreRank_comp_of_surjective (g : N →ₗ[O] P) {f : M →ₗ[O] N}
    (hf : Function.Surjective f) (q : PrimeSpectrum O) :
    fibreRank (g ∘ₗ f) q = fibreRank g q := by sorry
