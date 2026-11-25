-- Prove2me | Theorems.Thm_GlobalTheory_SingleBlock_phiU_mul_right
-- name    : GlobalTheory.SingleBlock.phiU_mul_right
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:50:40.08881+00:00
-- url     : https://prove2.me/theorems/d5ebbb8e-c274-457c-88e5-33ce0995b855
-- title:
--   Single Block: phi U mul right
-- statement:
--   The Single Block construction uses the phi U mul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HasCompactSupportPhiU.lean#L71-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HasCompactSupportPhiU.lean#L71-L82

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
variable {F : Type} [Field F] {r t : ℕ} {O : Subring F} {ϖ : F} {P : Subgroup (GL (Fin r) F)}

theorem GlobalTheory.SingleBlock.phiU_mul_right (hP : P ≤ GLint O r) (ρ : P →* ℂˣ) (g : P)
    (x : Matrix (Fin r ⊕ Fin t) (Fin r) F) :
    phiU O ϖ P ρ (x * ((g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) =
      ((ρ g : ℂˣ) : ℂ) * phiU O ϖ P ρ x := by sorry
