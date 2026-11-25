-- Prove2me | Theorems.Thm_GlobalTheory_LevelUnfold_glue_mem_gluedS_iff
-- name    : GlobalTheory.LevelUnfold.glue_mem_gluedS_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:18:36.062193+00:00
-- url     : https://prove2.me/theorems/715ad075-8355-54ad-a1a8-920be7d30f70
-- title:
--   Level Unfold: glue mem glued S iff
-- statement:
--   The Level Unfold construction uses the glue mem glued S iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemSmulOfMemFlagSubOne.lean#L89-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemSmulOfMemFlagSubOne.lean#L89-L102

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

theorem GlobalTheory.LevelUnfold.glue_mem_gluedS_iff (hc : 1 ≤ c) {L : Submodule 𝒪[k] (n → k)}
    {f x : n → k} :
    q.inv • _root_.GlobalTheory.LatPair.avec k n c 1 +
        _root_.GlobalTheory.LatPair.inX k n c x ∈ _root_.GlobalTheory.LatPair.gluedS q c L f ↔
      x - f ∈ L := by sorry
