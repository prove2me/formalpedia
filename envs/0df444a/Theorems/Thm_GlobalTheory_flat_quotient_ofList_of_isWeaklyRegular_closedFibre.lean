-- Prove2me | Theorems.Thm_GlobalTheory_flat_quotient_ofList_of_isWeaklyRegular_closedFibre
-- name    : GlobalTheory.flat_quotient_ofList_of_isWeaklyRegular_closedFibre
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:52:15.851305+00:00
-- url     : https://prove2.me/theorems/26385d66-de07-456b-be1e-e6fae94f3411
-- title:
--   Global Theory: flat quotient of List of is Weakly Regular closed Fibre
-- statement:
--   The Global Theory construction uses the flat quotient of List of is Weakly Regular closed Fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FlatQuotientWeaklyRegular.lean#L48-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FlatQuotientWeaklyRegular.lean#L48-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FlatCokerOfInjectiveModMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FlatQuotientWeaklyRegular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory

theorem GlobalTheory.flat_quotient_ofList_of_isWeaklyRegular_closedFibre : ∀ (V A : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Algebra V A] [IsLocalHom (algebraMap V A)] [Module.Flat V A] (rs : List A), (∀ r ∈ rs, r ∈ maximalIdeal A) → RingTheory.Sequence.IsWeaklyRegular (A ⧸ (maximalIdeal V).map (algebraMap V A)) rs → Module.Flat V (A ⧸ Ideal.ofList rs) := by sorry
