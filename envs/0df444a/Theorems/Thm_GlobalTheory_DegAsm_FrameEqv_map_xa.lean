-- Prove2me | Theorems.Thm_GlobalTheory_DegAsm_FrameEqv_map_xa
-- name    : GlobalTheory.DegAsm.FrameEqv.map_xa
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:21:44.912841+00:00
-- url     : https://prove2.me/theorems/9f07c96f-0155-463a-ab81-40fd3dcf88e2
-- title:
--   Frame Eqv: map xa
-- statement:
--   The Frame Eqv construction uses the map xa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FrEqvEquivalence.lean#L17-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FrEqvEquivalence.lean#L17-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsHermFramePairNormalFormMovedByIsometryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrEqvEquivalence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegAsm GlobalTheory.DegAsm.FrameEqv
open AdaptInv
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

theorem GlobalTheory.DegAsm.FrameEqv.map_xa {G G' : FlagD H r} {n : V ≃ₗ[K] V} (h : ∀ a : Fin (r + 1), n (G.e a) - G'.e a ∈ G'.Xa a.val)
    (k : ℕ) {x : V} (hx : x ∈ G.Xa k) : n x ∈ G'.Xa k := by sorry
