-- Prove2me | Theorems.Thm_OrderClosures_solid_generated_orderAdherence
-- name    : OrderClosures.solid_generated_orderAdherence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:11:07.11061+00:00
-- url     : https://prove2.me/theorems/7fe1f64f-2c6a-4730-bc64-15291883c077
-- title:
--   Order Closures: solid generated order Adherence
-- statement:
--   Paper Lemma `lem:solid-generated-order-adh`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L656-L756
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/GaoLeungProblem/Iterations.lean#L656-L756

module
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_StageFormula
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Definitions.Def_LeanPool_OrderClosures_GaoLeungProblem_Iterations
set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set
universe u v

theorem OrderClosures.solid_generated_orderAdherence
    {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [VectorLattice X] {G : Set X} (hG : G ⊆ Ici 0) :
    orderAdherence (solidHull G) =
      {x | ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·))
        (_ : Nonempty ι) (a : ι → X),
        (∀ i, a i ∈ G) ∧
          OrderConvergesTo (fun i ↦ |x| ⊓ a i) |x| ∧
          IsLUB (Set.range fun i ↦ |x| ⊓ a i) |x|} := by sorry
