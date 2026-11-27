-- Prove2me | Theorems.Thm_GlobalTheory_discr_norm_trace_of_isReduced
-- name    : GlobalTheory.discr_norm_trace_of_isReduced
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:47:20.566448+00:00
-- url     : https://prove2.me/theorems/8257d413-9357-4972-bc97-09c90e72a648
-- title:
--   Global Theory: discr norm trace of is Reduced
-- statement:
--   The Global Theory construction uses the discr norm trace of is Reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L324-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L324-L331

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCommensurableSpanSpanOfDetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing Polynomial
open scoped TensorProduct
open GlobalTheory
variable {K S L ι : Type*} [Field K] [PerfectField K] [CommRing S] [Algebra K S]
  [Module.Finite K S] [IsReduced S] [Field L] [Algebra K L] [IsSepClosed L] [Fintype ι]
  [DecidableEq ι]

theorem GlobalTheory.discr_norm_trace_of_isReduced (P : ι ≃ (S →ₐ[K] L)) :
    Fintype.card ι = finrank K S ∧
    (∀ v : ι → S, algebraMap K L (Algebra.discr K v) = (Matrix.of fun i j => P j (v i)).det ^ 2) ∧
    (∀ x : S, algebraMap K L (Algebra.norm K x) = ∏ j, P j x) ∧
    (∀ x : S, algebraMap K L (Algebra.trace K S x) = ∑ j, P j x) := by sorry
