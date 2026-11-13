-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_eta_eq_of_norm_one_regular_value_eq
-- name    : OddOrder.Peterfalvi.S16.eta_eq_of_norm_one_regular_value_eq
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:16:25.64729+00:00
-- url     : https://prove2.me/theorems/8765fb0f-8a81-4340-b68b-4c4b7b55e8ac
-- title:
--   Peterfalvi (3.9)(a): a norm-one virtual character agreeing with $\eta_A$ on the regular set equals $\eta_A$
-- statement:
--   Let $G$ be a finite group and `base : S15.Hypothesis` a Peterfalvi §13 configuration for $G$ with primes $p,q$, cyclic subgroups $W\supseteq W_1,W_2$ and grid characters $\eta_{ij}$. Let $\varphi\in\mathrm{ZIrr}(G)$ (a virtual character) with $\langle\varphi,\varphi\rangle = 1$, and $A=(i,j)\in\{0..q-1\}\times\{0..p-1\}$. Suppose $\varphi(w)=\eta_{A}(w)$ for every $w\in W$ with $w\notin W_1\cup W_2$. Then
--   $$\varphi=\eta_{A}.$$
--
--   The difference $\psi=\eta_A-\varphi$ vanishes on the conjugacy saturation of the regular set $\hat W=W\setminus(W_1\cup W_2)$, so its grid coefficients satisfy the (3.7) relation; each of $\eta_A,\varphi$ has norm one, so $\psi$ has at most two nonzero coefficients and the (3.8) small-support case forces $\psi=0$. This is the rigidity behind the independence of the $\sigma$-isometry construction.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/TGapGridAlignment.lean#L1135-L1243

import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_TGapNonorthogonality
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_TGapGridAlignment

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in

theorem eta_eq_of_norm_one_regular_value_eq [Finite G]
    (base : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    {φ : ClassFunction G ℂ} (hφZ : φ ∈ ZIrr G)
    (hφ1 : ClassFunction.inner φ φ = 1)
    (A : Fin base.q × Fin base.p)
    (hvals : ∀ w : G, w ∈ (base.W : Set G) →
      w ∉ (base.W1 : Set G) ∪ (base.W2 : Set G) →
      φ w = base.eta A.1 A.2 w) :
    φ = base.eta A.1 A.2 := by sorry

end OddOrder.Peterfalvi.S16
