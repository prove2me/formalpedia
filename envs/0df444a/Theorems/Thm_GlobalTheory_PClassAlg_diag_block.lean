-- Prove2me | Theorems.Thm_GlobalTheory_PClassAlg_diag_block
-- name    : GlobalTheory.PClassAlg.diag_block
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:09:50.714641+00:00
-- url     : https://prove2.me/theorems/24bb9a6b-a730-4c9e-a3ec-88fb8527b789
-- title:
--   PClass Alg: diag block
-- statement:
--   The PClass Alg construction uses the diag block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/DoubleBlockTriangularMemIntegralMulLevi.lean#L49-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/DoubleBlockTriangularMemIntegralMulLevi.lean#L49-L56

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

theorem GlobalTheory.PClassAlg.diag_block (B : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (h1 : B.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : B.BlockTriangular (fun r => OrderDual.toDual (lev p r))) :
    toBlocks₂₂ B = diagonal fun i => B (Sum.inr i) (Sum.inr i) := by sorry
