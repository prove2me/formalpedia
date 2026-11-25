-- Prove2me | Theorems.Thm_GlobalTheory_SingleBlock_hasCompactSupport_phiU
-- name    : GlobalTheory.SingleBlock.hasCompactSupport_phiU
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:49:26.192782+00:00
-- url     : https://prove2.me/theorems/691f50d5-fd53-46e2-9d12-d457932be145
-- title:
--   Single Block: has Compact Support phi U
-- statement:
--   The Single Block construction uses the has Compact Support phi U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HasCompactSupportPhiU.lean#L174-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HasCompactSupportPhiU.lean#L174-L180

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL
open GlobalTheory GlobalTheory.SingleBlock
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {r t : ℕ}
  {O : Subring F} {ϖ : F} {P : Subgroup (GL (Fin r) F)}

theorem GlobalTheory.SingleBlock.hasCompactSupport_phiU [T2Space F] (hO : IsCompact (O : Set F)) (hϖ : ϖ ∈ O)
    (hP : P ≤ GLint O r) (ρ : P →* ℂˣ) : HasCompactSupport (phiU (t := t) O ϖ P ρ) := by sorry
