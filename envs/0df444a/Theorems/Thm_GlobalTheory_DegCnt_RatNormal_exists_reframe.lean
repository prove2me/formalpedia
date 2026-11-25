-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_RatNormal_exists_reframe
-- name    : GlobalTheory.DegCnt.RatNormal.exists_reframe
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:26:45.949288+00:00
-- url     : https://prove2.me/theorems/50d33453-4b79-56be-8493-56b69787f6d6
-- title:
--   Rat Normal: exists reframe
-- statement:
--   The Rat Normal construction uses the exists reframe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsInvLower.lean#L38-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsInvLower.lean#L38-L54

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

theorem GlobalTheory.DegCnt.RatNormal.exists_reframe (F : FlagD H r) (f : Fin (r + 1) → V) (hf : ∀ a, f a - F.e a ∈ F.Xa a.val) :
    ∃ G : FlagD H r, G.e = f ∧ G.T = F.T ∧ ∀ n, G.Xa n = F.Xa n := by sorry
