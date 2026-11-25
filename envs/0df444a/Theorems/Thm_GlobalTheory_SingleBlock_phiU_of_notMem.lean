-- Prove2me | Theorems.Thm_GlobalTheory_SingleBlock_phiU_of_notMem
-- name    : GlobalTheory.SingleBlock.phiU_of_notMem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:49:46.074879+00:00
-- url     : https://prove2.me/theorems/a0477103-32f3-43ea-930f-43e2c55a8dfd
-- title:
--   Single Block: phi U of not Mem
-- statement:
--   The Single Block construction uses the phi U of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HasCompactSupportPhiU.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HasCompactSupportPhiU.lean#L27-L32

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

theorem GlobalTheory.SingleBlock.phiU_of_notMem (ρ : P →* ℂˣ) {x : Matrix (Fin r ⊕ Fin t) (Fin r) F}
    (hx : x ∉ suppSet t O ϖ P) : phiU O ϖ P ρ x = 0 := by sorry
