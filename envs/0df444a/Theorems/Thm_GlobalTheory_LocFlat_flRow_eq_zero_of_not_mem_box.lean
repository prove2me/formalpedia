-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_flRow_eq_zero_of_not_mem_box
-- name    : GlobalTheory.LocFlat.flRow_eq_zero_of_not_mem_box
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:10:52.745888+00:00
-- url     : https://prove2.me/theorems/5cd5ac23-e9cc-589d-a7eb-c212730df3a4
-- title:
--   Loc Flat: fl Row eq zero of not mem box
-- statement:
--   The Loc Flat construction uses the fl Row eq zero of not mem box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatMapRowEqZeroUnlessRowMemDualLattice.lean#L31-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatMapRowEqZeroUnlessRowMemDualLattice.lean#L31-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapRowEqZeroUnlessRowMemDualLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.LocFlat

theorem GlobalTheory.LocFlat.flRow_eq_zero_of_not_mem_box : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], ∀ j c (H : j + 1 + c = s) (r : ℕ), c = 2 * r → ∀ x : Matrix (XIx (Fin κ) t (j + 1) ⊕ Unit) (XIx (Fin κ) t j) k, x (Sum.inr ()) ∉ box (XIx (Fin κ) t j) (S.ϖ ^ (r + 1)) → GlobalTheory.LocFlat.flRow S.ψ ν (r + 1) ((S.T t).Phi j (c + 1) (by omega)) x = 0 := by sorry
