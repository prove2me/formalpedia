-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_BlockMinor_exists_block
-- name    : GlobalTheory.DegCnt.BlockMinor.exists_block
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:27:35.029164+00:00
-- url     : https://prove2.me/theorems/f129d0aa-fdaf-4491-ad22-ddb0298aaefa
-- title:
--   Block Minor: exists block
-- statement:
--   The Block Minor construction uses the exists block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFlagPairingCramerOfLeadingCoeffs.lean#L49-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFlagPairingCramerOfLeadingCoeffs.lean#L49-L78

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

theorem GlobalTheory.DegCnt.BlockMinor.exists_block (bs : List (Kˣ × ℕ+)) (a : ℕ) (ha : a < (bs.map fun b => (b.2 : ℕ)).sum) :
    ∃ (l s : ℕ) (t : Kˣ) (ε : ℤˣ), l ≤ a ∧ a < l + s ∧ l + s ≤ (bs.map fun b => (b.2 : ℕ)).sum ∧
      (∀ b, ptEntryL bs a b = if a + b + 1 = l + (l + s) then (t : K) else 0) ∧ minor bs l ≠ 0 ∧
      minor bs (l + s) = ((ε : ℤ) : K) * (t : K) ^ s * minor bs l := by sorry
