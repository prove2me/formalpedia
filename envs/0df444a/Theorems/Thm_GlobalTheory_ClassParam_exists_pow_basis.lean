-- Prove2me | Theorems.Thm_GlobalTheory_ClassParam_exists_pow_basis
-- name    : GlobalTheory.ClassParam.exists_pow_basis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:12.20559+00:00
-- url     : https://prove2.me/theorems/8ecfff54-bd8c-4ecd-9e19-9e71655fe0fa
-- title:
--   Class Param: exists pow basis
-- statement:
--   The Class Param construction uses the exists pow basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L601-L609
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L601-L609

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Matrix Formalism.UG
open GlobalTheory GlobalTheory.ClassParam
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion
attribute [local instance] algLk
variable {F E : Type} [Field F] [Field E] [Algebra F E] {c : E ≃ₐ[F] E} {r : ℕ} {P : E[X]}
  (k : Type) [Field k] [Algebra F k]

theorem GlobalTheory.ClassParam.exists_pow_basis (hP : IsPPol c r P) : ∃ b : Module.Basis (Fin r) E (AdjoinRoot P),
    (∀ i, b i = AdjoinRoot.root P ^ (i : ℕ)) ∧
      (Algebra.leftMulMatrix b (AdjoinRoot.root P)).charpoly = P := by sorry
