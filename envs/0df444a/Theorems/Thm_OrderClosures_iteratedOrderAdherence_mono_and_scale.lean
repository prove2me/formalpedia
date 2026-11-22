-- Prove2me | Theorems.Thm_OrderClosures_iteratedOrderAdherence_mono_and_scale
-- name    : OrderClosures.iteratedOrderAdherence_mono_and_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:55:54.760982+00:00
-- url     : https://prove2.me/theorems/9b12589e-96f2-42fa-80be-94fa8b3b8dad
-- title:
--   Order Closures: iterated Order Adherence mono and scale
-- statement:
--   Paper Lemma `lem:order-basic`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Reductions.lean#L36-L80
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/WeaklyFatou/Reductions.lean#L36-L80

module
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Reductions
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]

theorem OrderClosures.iteratedOrderAdherence_mono_and_scale
    {A B : Set X} {c : ℝ} (hc : 0 < c) :
    (A ⊆ B → ∀ m, iteratedOrderAdherence A m ⊆ iteratedOrderAdherence B m) ∧
      (orderAdherence (scaleSet c A) = scaleSet c (orderAdherence A) ∧
        ∀ m, iteratedOrderAdherence (scaleSet c A) m =
          scaleSet c (iteratedOrderAdherence A m)) := by sorry
