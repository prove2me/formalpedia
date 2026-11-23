-- Prove2me | Theorems.Thm_GlobalTheory_ClassParam_star_fixed_iff
-- name    : GlobalTheory.ClassParam.star_fixed_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:21:21.375804+00:00
-- url     : https://prove2.me/theorems/b40125e1-47c8-4b21-a7e9-a0a8a614a045
-- title:
--   Class Param: star fixed iff
-- statement:
--   The Class Param construction uses the star fixed iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L666-L669
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LeftMulMatrixTransfer.lean#L666-L669

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

theorem GlobalTheory.ClassParam.star_fixed_iff (hP : IsPPol c r P) (z : AdjoinRoot P ⊗[F] k) :
    starLk k hP z = z ↔ ∃ w, inclPlus k hP w = z := by sorry
