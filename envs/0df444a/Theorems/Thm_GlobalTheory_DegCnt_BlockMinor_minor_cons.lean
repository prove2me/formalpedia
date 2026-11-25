-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_BlockMinor_minor_cons
-- name    : GlobalTheory.DegCnt.BlockMinor.minor_cons
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:27:11.076943+00:00
-- url     : https://prove2.me/theorems/152a3890-015f-487e-be7a-44ecbc307e45
-- title:
--   Block Minor: minor cons
-- statement:
--   The Block Minor construction uses the minor cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFlagPairingCramerOfLeadingCoeffs.lean#L38-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFlagPairingCramerOfLeadingCoeffs.lean#L38-L47

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

theorem GlobalTheory.DegCnt.BlockMinor.minor_cons (t : Kˣ) (s : ℕ+) (bs : List (Kˣ × ℕ+)) (m : ℕ) : ∃ ε : ℤˣ,
    minor ((t, s) :: bs) (s + m) = ((ε : ℤ) : K) * (t : K) ^ (s : ℕ) * minor bs m := by sorry
