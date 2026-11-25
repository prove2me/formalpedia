-- Prove2me | Theorems.Thm_GlobalTheory_SingleBlock_weilPairing_self_eq_measure_support
-- name    : GlobalTheory.SingleBlock.weilPairing_self_eq_measure_support
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:50:39.8148+00:00
-- url     : https://prove2.me/theorems/f7ffd4f6-ccff-4d5e-ba4e-1156267e34ce
-- title:
--   Single Block: weil Pairing self eq measure support
-- statement:
--   The Single Block construction uses the weil Pairing self eq measure support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HasCompactSupportPhiU.lean#L295-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HasCompactSupportPhiU.lean#L295-L310

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

theorem GlobalTheory.SingleBlock.weilPairing_self_eq_measure_support (hS : MeasurableSet (suppSet t O ϖ P)) (ρ : P →* ℂˣ)
    (hρ : ∀ k, ‖((ρ k : ℂˣ) : ℂ)‖ = 1) (ν : Measure (Matrix (Fin r ⊕ Fin t) (Fin r) F)) :
    weilIP ν (phiU O ϖ P ρ) (phiU O ϖ P ρ) = ((ν (suppSet t O ϖ P)).toReal : ℂ) := by sorry
