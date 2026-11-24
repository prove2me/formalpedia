-- Prove2me | Theorems.Thm_GlobalTheory_T_tensorProduct_basis_coordinates
-- name    : GlobalTheory.T.tensorProduct_basis_coordinates
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:13:29.854658+00:00
-- url     : https://prove2.me/theorems/f1784d42-12d8-4357-b789-b1ab7d65b8de
-- title:
--   T: tensor Product basis coordinates
-- statement:
--   The T construction uses the tensor Product basis coordinates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TensorProductBasisCoordinatesStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TensorProductBasisCoordinatesStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorProductBasisCoordinates
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorProductBasisCoordinatesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.tensorProduct_basis_coordinates : ∀ (F : Type) [Field F] (B : Type) [CommRing B] [Algebra F B] (V : Type) [AddCommGroup V] [Module F V] (n : Type) [Fintype n] [DecidableEq n] (b : Basis n F V), ∃ e : V ⊗[F] B ≃ₗ[F] (n → B), (∀ v x i, e (v ⊗ₜ[F] x) i = b.repr v i • x) ∧ (∀ y : n → B, e.symm y = ∑ i, b i ⊗ₜ[F] y i) ∧ ∀ (r : V →ₗ[F] V) (f : B →ₗ[F] B) (y : V ⊗[F] B), e (TensorProduct.map r f y) = ((LinearMap.toMatrix b b r).map (algebraMap F B)).mulVec (fun i => f (e y i)) := by sorry
