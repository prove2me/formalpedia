-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_RatNormal_exists_ist
-- name    : GlobalTheory.DegCnt.RatNormal.exists_ist
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:14.142999+00:00
-- url     : https://prove2.me/theorems/5bb6aac1-2ebe-491f-8c95-6096a6fe33a8
-- title:
--   Rat Normal: exists ist
-- statement:
--   The Rat Normal construction uses the exists ist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsInvLower.lean#L150-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsInvLower.lean#L150-L190

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

theorem GlobalTheory.DegCnt.RatNormal.exists_ist [FiniteDimensional K V] [CharZero K] (G G' : FlagD H r) {j : ℕ} (hj : j ≤ r) {c : K} (hc : c ≠ 0)
    (same : ∀ a : Fin (r + 1), j ≤ a.val → G'.e a = c • G.e a)
    (hs : ∀ y, ∃ x ∈ G.X, ∀ u ∈ G'.Xa j, H.B u (y - x) = 0) :
    ∃ ist : Fin r → V, (∀ a b : Fin r, H.B (G.e a.castSucc) (ist b) = if a = b then 1 else 0) ∧
      (∀ b, ∀ u ∈ G'.Xa j, H.B u (ist b) = 0) ∧ (∀ b, H.B G.z (ist b) = 0) ∧
      ∀ a b : Fin r, j ≤ a.val → j ≤ b.val → H.B (ist a) (ist b) = 0 := by sorry
