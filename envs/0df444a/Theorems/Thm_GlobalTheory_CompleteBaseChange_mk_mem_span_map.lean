-- Prove2me | Theorems.Thm_GlobalTheory_CompleteBaseChange_mk_mem_span_map
-- name    : GlobalTheory.CompleteBaseChange.mk_mem_span_map
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:02:08.747948+00:00
-- url     : https://prove2.me/theorems/be41a204-762f-4b11-807f-4105602669bb
-- title:
--   Complete Base Change: mk mem span map
-- statement:
--   The Complete Base Change construction uses the mk mem span map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsPolynomialSubMem.lean#L119-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsPolynomialSubMem.lean#L119-L140

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsPolynomialSubMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries IsLocalRing
open scoped TensorProduct
open GlobalTheory GlobalTheory.CompleteBaseChange

theorem GlobalTheory.CompleteBaseChange.mk_mem_span_map : ∀ (T O : Type) [CommRing T] [CommRing O] [Algebra T O] (I : Ideal T), I.FG → IsAdicComplete (I.map (algebraMap T O)) O → ∀ (σ : Type) [Fintype σ] (f : σ → MvPowerSeries σ T), (∃ N : ℕ, ∀ α : σ →₀ ℕ, α.degree = N → (monomial α (1 : T) : MvPowerSeries σ T) ∈ Ideal.span (Set.range f) ⊔ I.map (MvPowerSeries.C : T →+* MvPowerSeries σ T)) → Module.Finite T (MvPowerSeries σ T ⧸ Ideal.span (Set.range f)) → ∀ g : MvPowerSeries σ O, Ideal.Quotient.mk (Ideal.span (Set.range fun j => MvPowerSeries.map (algebraMap T O) (f j))) g ∈ Submodule.span O (Set.range fun h : MvPowerSeries σ T => Ideal.Quotient.mk (Ideal.span (Set.range fun j => MvPowerSeries.map (algebraMap T O) (f j))) (MvPowerSeries.map (algebraMap T O) h)) := by sorry
