-- Prove2me | Theorems.Thm_GlobalTheory_SingleBlock_measure_suppSet
-- name    : GlobalTheory.SingleBlock.measure_suppSet
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:50:16.578676+00:00
-- url     : https://prove2.me/theorems/8ba8fece-2851-42de-b248-392382570613
-- title:
--   Single Block: measure supp Set
-- statement:
--   The Single Block construction uses the measure supp Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HasCompactSupportPhiU.lean#L257-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HasCompactSupportPhiU.lean#L257-L287

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
variable [MeasurableSpace F] [BorelSpace F]

theorem GlobalTheory.SingleBlock.measure_suppSet (hO : IsOpen (O : Set F)) (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0)
    (hloc : IsLocalAt O ϖ) [Finite (kF O ϖ hϖ)] (hKP : congSub O ϖ r ≤ P) (hP : P ≤ GLint O r)
    (ν : Measure (Matrix (Fin r ⊕ Fin t) (Fin r) F)) [ν.IsAddLeftInvariant] :
    ν (suppSet t O ϖ P) * (Nat.card (kF O ϖ hϖ) : ENNReal) ^ (r * r) *
        (Nat.card (kF O ϖ hϖ) : ENNReal) ^ (t * r) =
      (Nat.card (P ⧸ (congSub O ϖ r).subgroupOf P) : ENNReal) *
        ν (intMatrices O (Fin r ⊕ Fin t) (Fin r)) := by sorry
