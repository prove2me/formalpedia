-- Prove2me | Theorems.Thm_GlobalTheory_SingleBlock_nrm_det
-- name    : GlobalTheory.SingleBlock.nrm_det
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:54:51.065151+00:00
-- url     : https://prove2.me/theorems/93cf261e-836b-4311-b31f-7a41ddd03e31
-- title:
--   Single Block: nrm det
-- statement:
--   The Single Block construction uses the nrm det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/T2SpaceIsNonarchimedeanLocalFieldSingleBlock.lean#L173-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/T2SpaceIsNonarchimedeanLocalFieldSingleBlock.lean#L173-L179

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FromBlocksMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_T2SpaceIsNonarchimedeanLocalFieldSingleBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate ValuativeRel Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL
open GlobalTheory GlobalTheory.SingleBlock
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {r t : ℕ} {ϖ : 𝒪[F]}
omit [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GlobalTheory.SingleBlock.nrm_det {nrm : AbsoluteValue F ℝ} (hn : IsNormalisedAbs nrm) {n : Type} [Fintype n]
    [DecidableEq n] {g : GL n F} (hg : g ∈ glInt 𝒪[F] n) :
    nrm ((GeneralLinearGroup.det g : Fˣ) : F) = 1 := by sorry
