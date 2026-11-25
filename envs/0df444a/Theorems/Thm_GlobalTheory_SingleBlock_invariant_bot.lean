-- Prove2me | Theorems.Thm_GlobalTheory_SingleBlock_invariant_bot
-- name    : GlobalTheory.SingleBlock.invariant_bot
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:50:17.689993+00:00
-- url     : https://prove2.me/theorems/a56a070d-aa24-445a-ab31-8c403bc3e75b
-- title:
--   Single Block: invariant bot
-- statement:
--   The Single Block construction uses the invariant bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HasCompactSupportPhiU.lean#L241-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HasCompactSupportPhiU.lean#L241-L255

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

theorem GlobalTheory.SingleBlock.invariant_bot (ν : Measure (Matrix (Fin r ⊕ Fin t) (Fin r) F)) [ν.IsAddLeftInvariant]
    (A : Set (Matrix (Fin r) (Fin r) F)) :
    ((ν.restrict (toRows₁ ⁻¹' A)).map toRows₂).IsAddLeftInvariant := by sorry
