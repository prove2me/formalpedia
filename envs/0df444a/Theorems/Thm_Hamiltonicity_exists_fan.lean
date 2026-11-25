-- Prove2me | Theorems.Thm_Hamiltonicity_exists_fan
-- name    : Hamiltonicity.exists_fan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:16:33.720587+00:00
-- url     : https://prove2.me/theorems/9dbbc728-8b5a-57a7-a127-5f61523b8216
-- title:
--   Hamiltonicity: exists fan
-- statement:
--   **Fan lemma.**
--
--   Source: https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/ChvatalErdosAux.lean#L74-L160
-- source:
--   https://github.com/jtraverso/chvatal-posa-hamiltonian/blob/6be0ebda7b457b85ad400f6d7f92ad156d6e7712/MengerHamilton/ChvatalErdosAux.lean#L74-L160

module
public import Definitions.Def_MengerHamilton_LongerCycle
public import Definitions.Def_MengerHamilton_ChvatalErdosAux
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Hamiltonicity
variable {V : Type*}

theorem Hamiltonicity.exists_fan [Finite V] {G : SimpleGraph V} {k : ℕ}
    (hconn : ∀ S : Set V, S.ncard < k → (G.induce Sᶜ).Connected)
    {m : ℕ} {f : ℕ → V} (hC : CycArr G m f) {x : V} (hx : ∀ i, f i ≠ x) :
    ∃ r, min k m ≤ r ∧ ∃ (t : Fin r → ℕ) (P : ∀ j, G.Walk x (f (t j))),
      (∀ j, (P j).IsPath) ∧ (∀ j, ∀ y ∈ (P j).support, ∀ i, f i = y → y = f (t j)) ∧
      (∀ i j, i ≠ j → ∀ y ∈ (P i).support, y ∈ (P j).support → y = x) := by sorry
