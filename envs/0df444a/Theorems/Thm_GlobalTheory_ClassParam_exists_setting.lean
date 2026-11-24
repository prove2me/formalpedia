-- Prove2me | Theorems.Thm_GlobalTheory_ClassParam_exists_setting
-- name    : GlobalTheory.ClassParam.exists_setting
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:21:45.220927+00:00
-- url     : https://prove2.me/theorems/ab7e6efe-5466-4c0d-84b2-d841dff49080
-- title:
--   Class Param: exists setting
-- statement:
--   The Class Param construction uses the exists setting property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L618-L652
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L618-L652

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

theorem GlobalTheory.ClassParam.exists_setting [CharZero E] (hP : IsPPol c r P) (hc : ∀ e, c (c e) = e) :
    ∃ b : Module.Basis (Fin r) (E ⊗[F] k) (AdjoinRoot P ⊗[F] k),
      HidaSetting (sigR (c : E →ₐ[F] E) k) (starLk k hP) (AdjoinRoot.root P ⊗ₜ[F] (1 : k)) b ∧
      (Algebra.leftMulMatrix b (AdjoinRoot.root P ⊗ₜ[F] (1 : k))).charpoly
        = P.map (inclE (F := F) k) := by sorry
