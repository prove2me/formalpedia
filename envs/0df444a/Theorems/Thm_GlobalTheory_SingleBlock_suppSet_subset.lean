-- Prove2me | Theorems.Thm_GlobalTheory_SingleBlock_suppSet_subset
-- name    : GlobalTheory.SingleBlock.suppSet_subset
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:51:00.017336+00:00
-- url     : https://prove2.me/theorems/b355b5a5-ae31-48cc-814f-9d8c95a0208d
-- title:
--   Single Block: supp Set subset
-- statement:
--   The Single Block construction uses the supp Set subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HasCompactSupportPhiU.lean#L146-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HasCompactSupportPhiU.lean#L146-L153

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

theorem GlobalTheory.SingleBlock.suppSet_subset (hϖ : ϖ ∈ O) (hP : P ≤ GLint O r) :
    suppSet t O ϖ P ⊆ intMatrices O (Fin r ⊕ Fin t) (Fin r) := by sorry
