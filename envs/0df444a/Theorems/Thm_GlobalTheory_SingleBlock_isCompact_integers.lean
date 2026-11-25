-- Prove2me | Theorems.Thm_GlobalTheory_SingleBlock_isCompact_integers
-- name    : GlobalTheory.SingleBlock.isCompact_integers
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:55:27.1349+00:00
-- url     : https://prove2.me/theorems/eb6f0f0b-513d-489f-9060-164e2a47814a
-- title:
--   Single Block: is Compact integers
-- statement:
--   The Single Block construction uses the is Compact integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/T2SpaceIsNonarchimedeanLocalFieldSingleBlock.lean#L75-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/T2SpaceIsNonarchimedeanLocalFieldSingleBlock.lean#L75-L76

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

theorem GlobalTheory.SingleBlock.isCompact_integers : IsCompact ((𝒪[F] : Subring F) : Set F) := by sorry
