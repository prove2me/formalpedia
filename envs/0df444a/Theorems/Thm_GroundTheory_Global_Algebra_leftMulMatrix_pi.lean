-- Prove2me | Theorems.Thm_GroundTheory_Global_Algebra_leftMulMatrix_pi
-- name    : GroundTheory.Global.Algebra.leftMulMatrix_pi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:55:41.293178+00:00
-- url     : https://prove2.me/theorems/b820f588-7189-433d-aaaf-ff99fef6b309
-- title:
--   Algebra: left Mul Matrix pi
-- statement:
--   The Algebra construction uses the left Mul Matrix pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Infinite.lean#L44-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Infinite.lean#L44-L53

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.LiesOver TensorProduct
open GroundTheory.Global.Algebra
variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] {A : ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] [∀ i, Module.Free R (A i)]
  [∀ i, Module.Finite R (A i)]
omit [∀ i, Module.Free R (A i)] [∀ i, Module.Finite R (A i)]

theorem GroundTheory.Global.Algebra.leftMulMatrix_pi {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (b : ∀ i, Module.Basis (κ i) R (A i)) (x : ∀ i, A i) :
    Algebra.leftMulMatrix (Pi.basis b) x =
      Matrix.blockDiagonal' fun i => Algebra.leftMulMatrix (b i) (x i) := by sorry
