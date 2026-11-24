-- Prove2me | Theorems.Thm_GlobalTheory_LevelUnfold_mem_gluedS
-- name    : GlobalTheory.LevelUnfold.mem_gluedS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:26:01.432573+00:00
-- url     : https://prove2.me/theorems/5a7dba18-c404-459b-9ccb-64573be6a98d
-- title:
--   Level Unfold: mem glued S
-- statement:
--   The Level Unfold construction uses the mem glued S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemSmulOfMemFlagSubOne.lean#L28-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemSmulOfMemFlagSubOne.lean#L28-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FlagVolumeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemSmulOfMemFlagSubOne
import Theorems.Thm_GlobalTheory_RootEx_Radical_Uni_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise ENNReal
noncomputable section
open GlobalTheory GlobalTheory.LevelUnfold
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ} {q : Unif k}
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise ENNReal
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ} {q : _root_.GlobalTheory.LatPair.Unif k}

theorem GlobalTheory.LevelUnfold.mem_gluedS {L : Submodule 𝒪[k] (n → k)} {f : n → k}
    {y : n ⊕ Fin c → k} :
    y ∈ _root_.GlobalTheory.LatPair.gluedS q c L f ↔ ∃ s : 𝒪[k], y ∘ Sum.inl - s • f ∈ L ∧ ∀ i : Fin c,
      (i.val = 0 → y (Sum.inr i) = q.inv * s) ∧
        (0 < i.val → (q.1 : k) * y (Sum.inr i) ∈ 𝒪[k]) := by sorry
