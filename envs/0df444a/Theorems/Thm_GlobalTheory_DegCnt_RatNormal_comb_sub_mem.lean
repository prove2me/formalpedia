-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_RatNormal_comb_sub_mem
-- name    : GlobalTheory.DegCnt.RatNormal.comb_sub_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:25:42.728776+00:00
-- url     : https://prove2.me/theorems/5bd35d89-cfe0-5c05-bd6b-5dde1fb941d8
-- title:
--   Rat Normal: comb sub mem
-- statement:
--   The Rat Normal construction uses the comb sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsInvLower.lean#L78-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsInvLower.lean#L78-L86

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsInvLower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.HermitianLatticeCounting.P
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.RatNormal
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}

theorem GlobalTheory.DegCnt.RatNormal.comb_sub_mem (F : FlagD H r) {j : ℕ} (hj : j ≤ r) (M : Matrix (Fin j) (Fin j) K)
    (h0 : ∀ a b, a < b → M a b = 0) (h1 : ∀ a, M a a = 1) (a : Fin j) :
    ∑ b, M a b • F.e (Fin.castLE (hj.trans (Nat.le_succ r)) b) - F.e (Fin.castLE (hj.trans (Nat.le_succ r)) a) ∈
      F.Xa a.val := by sorry
