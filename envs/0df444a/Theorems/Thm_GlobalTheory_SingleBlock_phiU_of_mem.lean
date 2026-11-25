-- Prove2me | Theorems.Thm_GlobalTheory_SingleBlock_phiU_of_mem
-- name    : GlobalTheory.SingleBlock.phiU_of_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:49:30.863832+00:00
-- url     : https://prove2.me/theorems/63e85a8f-cabe-419b-8840-30009e816dd5
-- title:
--   Single Block: phi U of mem
-- statement:
--   The Single Block construction uses the phi U of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HasCompactSupportPhiU.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HasCompactSupportPhiU.lean#L19-L25

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

theorem GlobalTheory.SingleBlock.phiU_of_mem (ρ : P →* ℂˣ) {x : Matrix (Fin r ⊕ Fin t) (Fin r) F} (k : P)
    (hk : ((k : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = toRows₁ x)
    (h2 : toRows₂ x ∈ IIset O ϖ) : phiU O ϖ P ρ x = ((ρ k : ℂˣ) : ℂ) := by sorry
