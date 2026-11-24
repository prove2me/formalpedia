-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_RestrictedProduct_matrixUnitsEquiv_apply
-- name    : GroundTheory.Automorphic.RestrictedProduct.matrixUnitsEquiv_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:27:16.257247+00:00
-- url     : https://prove2.me/theorems/a526ee1d-69f7-486e-a518-691c74cff0fe
-- title:
--   Restricted Product: matrix Units Equiv apply
-- statement:
--   The Restricted Product construction uses the matrix Units Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RestrictedProductMatrix.lean#L280-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/RestrictedProductMatrix.lean#L280-L283

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Restricted
import Definitions.Def_GroundTheory_AutomorphicForms_RestrictedProductMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Filter Topology Set
open scoped RestrictedProduct
noncomputable section
open GroundTheory.Automorphic.RestrictedProduct
variable {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)]
variable (m : Type*) [Fintype m] [DecidableEq m]
variable [∀ i, Ring (R i)] {S : ι → Type*} [∀ i, SetLike (S i) (R i)]
  [∀ i, SubringClass (S i) (R i)] {B : Π i, S i} {C : Π i, Subring (Matrix m m (R i))}

theorem GroundTheory.Automorphic.RestrictedProduct.matrixUnitsEquiv_apply (hC : ∀ i (M : Matrix m m (R i)), M ∈ C i ↔ ∀ a b, M a b ∈ B i)
    (hB : ∀ i, IsOpen (B i : Set (R i))) (g : GL m (Πʳ i, [R i, B i])) (i : ι) (a b : m) :
    (matrixUnitsEquiv m hC hB g i : Matrix m m (R i)) a b = g a b i := by sorry

attribute [defeq] GroundTheory.Automorphic.RestrictedProduct.matrixUnitsEquiv_apply
