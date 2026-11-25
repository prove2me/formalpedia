-- Prove2me | Theorems.Thm_GlobalTheory_DegAsm_NFUnique_wt_e
-- name    : GlobalTheory.DegAsm.NFUnique.wt_e
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:21:25.909154+00:00
-- url     : https://prove2.me/theorems/5f643f9c-062b-5c25-86b2-47a3b281437e
-- title:
--   NFUnique: wt e
-- statement:
--   The NFUnique construction uses the wt e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormUniqueUpToUnipotent.lean#L91-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairNormalFormUniqueUpToUnipotent.lean#L91-L92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FlagFramesSameGradedDefinitePartLatticeEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormUniqueUpToUnipotent
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
open Formalism.HermitianLatticeCounting.P
open GlobalTheory GlobalTheory.DegAsm GlobalTheory.DegAsm.NFUnique
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}
variable [NumberField K]

theorem GlobalTheory.DegAsm.NFUnique.wt_e (N : NF H r) {w : V} (hw : w ∈ N.Wt) (a : Fin (r + 1)) : H.B (N.F.e a) w = 0 := by sorry
