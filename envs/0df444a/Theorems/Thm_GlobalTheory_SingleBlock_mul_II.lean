-- Prove2me | Theorems.Thm_GlobalTheory_SingleBlock_mul_II
-- name    : GlobalTheory.SingleBlock.mul_II
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:50:04.812666+00:00
-- url     : https://prove2.me/theorems/a4d54742-c5b8-4fe2-871a-48437eed99e4
-- title:
--   Single Block: mul II
-- statement:
--   The Single Block construction uses the mul II property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HasCompactSupportPhiU.lean#L41-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HasCompactSupportPhiU.lean#L41-L46

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

theorem GlobalTheory.SingleBlock.mul_II {l m n : ℕ} {A : Matrix (Fin l) (Fin m) F} (hA : ∀ i j, A i j ∈ O)
    {y : Matrix (Fin m) (Fin n) F} (hy : y ∈ IIset O ϖ) : A * y ∈ IIset O ϖ := by sorry
