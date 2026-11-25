-- Prove2me | Theorems.Thm_GlobalTheory_SingleBlock_mul_right_mem
-- name    : GlobalTheory.SingleBlock.mul_right_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:50:12.422765+00:00
-- url     : https://prove2.me/theorems/509af851-34ed-4f03-a2fd-4fcec97dcff1
-- title:
--   Single Block: mul right mem
-- statement:
--   The Single Block construction uses the mul right mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HasCompactSupportPhiU.lean#L57-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HasCompactSupportPhiU.lean#L57-L69

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

theorem GlobalTheory.SingleBlock.mul_right_mem (hP : P ≤ GLint O r) (ρ : P →* ℂˣ) (g : P)
    {x : Matrix (Fin r ⊕ Fin t) (Fin r) F} (hx : x ∈ suppSet t O ϖ P) :
    x * ((g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) ∈ suppSet t O ϖ P ∧
      phiU O ϖ P ρ (x * ((g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) =
        ((ρ g : ℂˣ) : ℂ) * phiU O ϖ P ρ x := by sorry
