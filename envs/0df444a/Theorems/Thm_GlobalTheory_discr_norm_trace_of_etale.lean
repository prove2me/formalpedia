-- Prove2me | Theorems.Thm_GlobalTheory_discr_norm_trace_of_etale
-- name    : GlobalTheory.discr_norm_trace_of_etale
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:44:41.267658+00:00
-- url     : https://prove2.me/theorems/82dcd453-5c06-5d11-be30-f1820dbea4e5
-- title:
--   Global Theory: discr norm trace of etale
-- statement:
--   The Global Theory construction uses the discr norm trace of etale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L308-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin.lean#L308-L314

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
variable (K : Type*) {S : Type*} (L : Type*) [Field K] [CommRing S] [Algebra K S] [Field L]
  [Algebra K L] [IsSepClosed L] [Algebra.Etale K S]
variable {K L} {ι : Type*} [Fintype ι]

theorem GlobalTheory.discr_norm_trace_of_etale [DecidableEq ι] (P : ι ≃ (S →ₐ[K] L)) :
    Fintype.card ι = finrank K S ∧
    (∀ v : ι → S, algebraMap K L (Algebra.discr K v) = (Matrix.of fun i j => P j (v i)).det ^ 2) ∧
    (∀ x : S, algebraMap K L (Algebra.norm K x) = ∏ j, P j x) ∧
    (∀ x : S, algebraMap K L (Algebra.trace K S x) = ∑ j, P j x) := by sorry
