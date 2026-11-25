-- Prove2me | Theorems.Thm_GlobalTheory_LevelUnfold_mul_coord_mem
-- name    : GlobalTheory.LevelUnfold.mul_coord_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:13:35.163961+00:00
-- url     : https://prove2.me/theorems/a1b06a71-fae4-4c65-ae68-ac0d443fa7a8
-- title:
--   Level Unfold: mul coord mem
-- statement:
--   The Level Unfold construction uses the mul coord mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemSmulOfMemFlagSubOne.lean#L104-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemSmulOfMemFlagSubOne.lean#L104-L110

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FlagVolumeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemSmulOfMemFlagSubOne
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

theorem GlobalTheory.LevelUnfold.mul_coord_mem {L : Submodule 𝒪[k] (n → k)} {f : n → k} {y : n ⊕ Fin c → k} (hy : y ∈ gluedS q c L f)
    (i : Fin c) : (q.1 : k) * y (Sum.inr i) ∈ 𝒪[k] := by sorry
