-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_BlockMinor_minor_full
-- name    : GlobalTheory.DegCnt.BlockMinor.minor_full
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:26:23.077739+00:00
-- url     : https://prove2.me/theorems/971ab315-59a6-5c25-9413-e16e3d62ae21
-- title:
--   Block Minor: minor full
-- statement:
--   The Block Minor construction uses the minor full property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFlagPairingCramerOfLeadingCoeffs.lean#L80-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFlagPairingCramerOfLeadingCoeffs.lean#L80-L91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemOfForall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFlagPairingCramerOfLeadingCoeffs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.BlockMinor
variable {K : Type} [Field K]

theorem GlobalTheory.DegCnt.BlockMinor.minor_full (bs : List (Kˣ × ℕ+)) : minor bs (bs.map fun b => (b.2 : ℕ)).sum ≠ 0 := by sorry
