-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_eta_cross_expansion_ne_zero
-- name    : OddOrder.Peterfalvi.S15.eta_cross_expansion_ne_zero
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T15:41:29.410189+00:00
-- url     : https://prove2.me/theorems/a99b4336-2a73-4034-b1e5-7511970bf42a
-- title:
--   Peterfalvi (13.4): the cross expansion of the grid-corrected pair $\lambda^\circ,\theta^\circ$ is nonzero
-- statement:
--   Let $G$ be a finite group (`Fintype G`, $|G|$ invertible in $\mathbb C$), let $q,p$ be natural numbers and $\eta:\{0,\dots,q-1\}\times\{0,\dots,p-1\}\to\mathrm{CF}(G)$ an orthonormal family of class functions: $\langle\eta_{ij},\eta_{kl}\rangle=1$ if $(i,j)=(k,l)$ and $0$ otherwise. Let $\lambda,\theta$ be class functions on $G$ with $\langle\lambda,\theta\rangle=0$, $\langle\lambda,\eta_{ij}\rangle=0$ and $\langle\eta_{ij},\theta\rangle=0$ for all $i,j$. Let $r<q$, $s<p$ and $\delta,\delta'\in\{1,-1\}$. Then
--
--   $$\Big\langle\lambda-\delta\sum_{i<q}\eta_{is},\ \theta-\delta'\sum_{j<p}\eta_{rj}\Big\rangle\ne0 .$$
--
--   In (13.4) the left side is $(\alpha^\tau,\beta^\tau)$, which vanishes by disjointness of TI-supports; this contradiction closes (13.4).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndT_Setup/Machinery135.lean#L295-L344

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_HypothesisBasics
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Machinery135

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

theorem eta_cross_expansion_ne_zero [Fintype G] [Invertible (Nat.card G : ℂ)] {q p : ℕ}
    (eta : Fin q → Fin p → ClassFunction G ℂ)
    (horth : ∀ (i k : Fin q) (j l : Fin p),
      ClassFunction.inner (eta i j) (eta k l) = if i = k ∧ j = l then 1 else 0)
    (lam theta : ClassFunction G ℂ) (r : Fin q) (s : Fin p)
    (hlam_eta : ∀ (i : Fin q) (j : Fin p), ClassFunction.inner lam (eta i j) = 0)
    (heta_theta : ∀ (i : Fin q) (j : Fin p), ClassFunction.inner (eta i j) theta = 0)
    (hlam_theta : ClassFunction.inner lam theta = 0)
    {δ δ' : ℤ} (hδ : δ = 1 ∨ δ = -1) (hδ' : δ' = 1 ∨ δ' = -1) :
    ClassFunction.inner (lam - (δ : ℂ) • ∑ i : Fin q, eta i s)
      (theta - (δ' : ℂ) • ∑ j : Fin p, eta r j) ≠ 0 := by sorry

end OddOrder.Peterfalvi.S15
