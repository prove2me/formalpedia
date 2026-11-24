-- Prove2me | Theorems.Thm_GlobalTheory_LevelUnfold_glue_mem_gluedS
-- name    : GlobalTheory.LevelUnfold.glue_mem_gluedS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:37.617046+00:00
-- url     : https://prove2.me/theorems/408ea238-a069-4516-a861-bbf18e3ed82f
-- title:
--   Level Unfold: glue mem glued S
-- statement:
--   The Level Unfold construction uses the glue mem glued S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemSmulOfMemFlagSubOne.lean#L79-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemSmulOfMemFlagSubOne.lean#L79-L83

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

theorem GlobalTheory.LevelUnfold.glue_mem_gluedS (L : Submodule 𝒪[k] (n → k)) (f : n → k) :
    q.inv • _root_.GlobalTheory.LatPair.avec k n c 1 +
      _root_.GlobalTheory.LatPair.inX k n c f ∈ _root_.GlobalTheory.LatPair.gluedS q c L f := by sorry
