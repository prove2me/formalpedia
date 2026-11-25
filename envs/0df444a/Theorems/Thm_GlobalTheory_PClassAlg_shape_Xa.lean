-- Prove2me | Theorems.Thm_GlobalTheory_PClassAlg_shape_Xa
-- name    : GlobalTheory.PClassAlg.shape_Xa
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:09:21.540125+00:00
-- url     : https://prove2.me/theorems/5bc32916-4b14-50fd-b32c-98c74b8d17d5
-- title:
--   PClass Alg: shape Xa
-- statement:
--   The PClass Alg construction uses the shape Xa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/DoubleBlockTriangularMemIntegralMulLevi.lean#L31-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/DoubleBlockTriangularMemIntegralMulLevi.lean#L31-L39

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

theorem GlobalTheory.PClassAlg.shape_Xa (B : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (h1 : B.BlockTriangular (Sum.elim (fun _ : n => 2 * p - 1) (fun i : Fin c => 2 * (i.val + 1))))
    (h2 : B.BlockTriangular (fun r => OrderDual.toDual (lev p r))) (x : n) (i : Fin c) (hi : i.val + 1 ≠ p) :
    B (Sum.inl x) (Sum.inr i) = 0 := by sorry
