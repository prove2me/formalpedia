-- Prove2me | Theorems.Thm_GlobalTheory_finite_card_trace_algHom_of_isReduced_baseChange
-- name    : GlobalTheory.finite_card_trace_algHom_of_isReduced_baseChange
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:27:02.315227+00:00
-- url     : https://prove2.me/theorems/2288da23-7c4d-4604-96d1-c3e7d402c8b6
-- title:
--   Global Theory: finite card trace alg Hom of is Reduced base Change
-- statement:
--   The Global Theory construction uses the finite card trace alg Hom of is Reduced base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CardAlgHomReducedTraceSum.lean#L8-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CardAlgHomReducedTraceSum.lean#L8-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CardAlgHomReducedTraceSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.finite_card_trace_algHom_of_isReduced_baseChange :
    ∀ (O H K : Type) [CommRing O] [Nontrivial O] [CommRing H] [Algebra O H] [Module.Free O H]
      [Module.Finite O H] [Field K] [IsAlgClosed K] [Algebra O K], IsReduced (K ⊗[O] H) →
      Finite (H →ₐ[O] K) ∧ Nat.card (H →ₐ[O] K) = Module.finrank O H ∧
        ∀ h : H, algebraMap O K (Algebra.trace O H h) = ∑ᶠ ga : H →ₐ[O] K, ga h := by sorry
