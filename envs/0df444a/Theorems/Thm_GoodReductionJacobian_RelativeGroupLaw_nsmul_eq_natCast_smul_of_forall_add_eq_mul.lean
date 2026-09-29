-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_nsmul_eq_natCast_smul_of_forall_add_eq_mul
-- name    : GoodReductionJacobian.RelativeGroupLaw.nsmul_eq_natCast_smul_of_forall_add_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/9e46fa09-1a14-5a8b-ba57-98074ad88d76
-- title:
--   [n] acts as n on an additive presentation of tangent vectors
-- statement:
--   Let $B$ be a commutative ring, let $A$ be a scheme and let $f : A \to \operatorname{Spec} B$ be a morphism carrying a relative group law $L$, i.e. for every scheme $T$ and every $t : T \to \operatorname{Spec} B$ a multiplication, a unit and an inversion on the set of $t$-sections $\{\varphi : T \to A \mid \varphi \text{ followed by } f = t\}$, subject to associativity, the two unit laws, left inverses, and compatibility of the multiplication with precomposition by any $\psi : T' \to T$ over $\operatorname{Spec} B$. Let $k$ be a field with a ring homomorphism $s_k : B \to k$, and write `tangentBase k sk` for the induced morphism $\operatorname{Spec} k[\varepsilon] \to \operatorname{Spec} B$ obtained from $B \to k \to k[\varepsilon]$, where $k[\varepsilon]$ is the dual numbers over $k$. Let $W$ be a $k$-vector space and $\tau : W \to \{\varphi : \operatorname{Spec} k[\varepsilon] \to A \mid \varphi \text{ followed by } f = \mathtt{tangentBase}\,k\,s_k\}$ a map which is additive for the group law, $\tau(v + w) = L.\mathrm{mul}(\tau v, \tau w)$. Then for every $n \in \mathbb{N}$ and $w \in W$ the $n$-fold product `L.nsmul` of $\tau(w)$ with itself (defined by recursion from the unit) equals $\tau((n : k) \cdot w)$, and moreover if $(n : k) = 0$ in $k$ then that $n$-fold product is the unit section $L.\mathrm{one}$.
--
--   This is the statement that on tangent vectors at the unit section of a relative group law the multiplication-by-$n$ map is the scalar $n$, so that $[n]$ kills the tangent space whenever $n$ vanishes in the residue field $k$. It is used in the construction of nontrivial $k[\varepsilon]$-points killed by $[n]$, via [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_nsmul_eq_one_dualNumber_ne_one_of_natCast_eq_zero`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_nsmul_eq_one_dualNumber_ne_one_of_natCast_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_nsmul_eq_natCast_smul_of_forall_add_eq_mul.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem GoodReductionJacobian.RelativeGroupLaw.nsmul_eq_natCast_smul_of_forall_add_eq_mul
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)
    (k : Type) [Field k] (sk : B →+* k)
    (W : Type) [AddCommGroup W] [Module k W]
    (τ : W → SchemeHomOver (tangentBase k sk) f)
    (hadd : ∀ v w : W, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w))
    (n : ℕ) (w : W) :
    L.nsmul (tangentBase k sk) n (τ w) = τ ((n : k) • w) ∧
      ((n : k) = 0 → L.nsmul (tangentBase k sk) n (τ w) = L.one (tangentBase k sk)) := by sorry
