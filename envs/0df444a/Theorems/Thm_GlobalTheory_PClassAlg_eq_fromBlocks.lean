-- Prove2me | Theorems.Thm_GlobalTheory_PClassAlg_eq_fromBlocks
-- name    : GlobalTheory.PClassAlg.eq_fromBlocks
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:09:29.257518+00:00
-- url     : https://prove2.me/theorems/2dd96e63-6885-5937-a4fa-30b3dc231f07
-- title:
--   PClass Alg: eq from Blocks
-- statement:
--   The PClass Alg construction uses the eq from Blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/DoubleBlockTriangularMemIntegralMulLevi.lean#L41-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/DoubleBlockTriangularMemIntegralMulLevi.lean#L41-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_DoubleBlockTriangularMemIntegralMulLevi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.PClassAlg
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem GlobalTheory.PClassAlg.eq_fromBlocks (hp : 1 ≤ p) (B : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (h1 : B.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : B.BlockTriangular (fun r => OrderDual.toDual (lev p r))) :
    B = fromBlocks (toBlocks₁₁ B) (toBlocks₁₂ B) 0 (toBlocks₂₂ B) := by sorry
