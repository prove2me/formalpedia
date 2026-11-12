-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch04_prime_dvd_card_of_faithful_iterCommutator_eq_bot
-- name    : OddOrder.Isaacs.Ch04.prime_dvd_card_of_faithful_iterCommutator_eq_bot
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:18:26.316371+00:00
-- url     : https://prove2.me/theorems/e394ddbd-aad5-4ac1-9443-5e6aa8915c2e
-- title:
--   Isaacs Corollary 4.30: faithful action with trivial iterated commutator forces prime divisors of $|A|$ to divide $|G|$
-- statement:
--   Let $A$ and $G$ be finite groups and $\varphi:A\to\mathrm{Aut}(G)$ an injective homomorphism (a faithful action of $A$ on $G$). Let $m\ge1$ and suppose the $m$-fold iterated commutator
--   $$[G,\underbrace{A,\dots,A}_{m}]=1$$
--   in the semidirect product $G\rtimes_\varphi A$ (with $G$ and $A$ identified with their images). Then every prime $p$ dividing $|A|$ divides $|G|$:
--   $$p\mid|A|\ \Longrightarrow\ p\mid|G|.$$
--
--   For a prime $p\nmid|G|$, one restricts to a Sylow $p$-subgroup $P\le A$: the action is coprime, the chain hypothesis restricts to $P$, Lemma 4.29 collapses it to $[G,P]=1$, and faithfulness forces $P=1$.
--
--   **Formalization Note** The iterated commutator is `iterCommutator E F m`, defined by $E_0=E$ and $E_{n+1}=[E_n,F]$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch04_Commutators/Main/ThreeSubgroupsCoprime.lean#L681-L743

import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroups
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime

namespace OddOrder.Isaacs.Ch04

open scoped commutatorElement

variable {G : Type*} [Group G]

section

theorem prime_dvd_card_of_faithful_iterCommutator_eq_bot
    {A G : Type*} [Group A] [Group G] [Finite A] [Finite G]
    (φ : A →* MulAut G) (h_inj : Function.Injective φ)
    {m : ℕ} (hm : 1 ≤ m)
    (h_iter : iterCommutator (SemidirectProduct.inl : G →* G ⋊[φ] A).range
        (SemidirectProduct.inr : A →* G ⋊[φ] A).range m = ⊥)
    {p : ℕ} (hp : p.Prime) (hpA : p ∣ Nat.card A) :
    p ∣ Nat.card G := by sorry

end

end OddOrder.Isaacs.Ch04
