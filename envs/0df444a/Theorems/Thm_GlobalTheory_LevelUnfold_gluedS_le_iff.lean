-- Prove2me | Theorems.Thm_GlobalTheory_LevelUnfold_gluedS_le_iff
-- name    : GlobalTheory.LevelUnfold.gluedS_le_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:03:37.079245+00:00
-- url     : https://prove2.me/theorems/85f6eba4-9dcc-4696-9142-f304d14458be
-- title:
--   Level Unfold: glued S le iff
-- statement:
--   The Level Unfold construction uses the glued S le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemSmulOfMemFlagSubOne.lean#L46-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemSmulOfMemFlagSubOne.lean#L46-L62

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

theorem GlobalTheory.LevelUnfold.gluedS_le_iff {L : Submodule 𝒪[k] (n → k)} {f : n → k}
    {M : Submodule 𝒪[k] (n ⊕ Fin c → k)} :
    _root_.GlobalTheory.LatPair.gluedS q c L f ≤ M ↔ (∀ y ∈ L, _root_.GlobalTheory.LatPair.inX k n c y ∈ M) ∧
      q.inv • _root_.GlobalTheory.LatPair.avec k n c 1 +
          _root_.GlobalTheory.LatPair.inX k n c f ∈ M ∧
      ∀ i : Fin c, 0 < i.val →
        q.inv • _root_.GlobalTheory.LatPair.avec k n c (i.val + 1) ∈ M := by sorry
