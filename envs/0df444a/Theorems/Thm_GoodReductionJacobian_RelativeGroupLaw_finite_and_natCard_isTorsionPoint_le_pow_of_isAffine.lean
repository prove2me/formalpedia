-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_finite_and_natCard_isTorsionPoint_le_pow_of_isAffine
-- name    : GoodReductionJacobian.RelativeGroupLaw.finite_and_natCard_isTorsionPoint_le_pow_of_isAffine
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/6bf35d2f-9dca-5969-a23e-b47c86a353ef
-- title:
--   Torsion bound m^h for connected commutative affine group laws
-- statement:
--   Let $k$ be an algebraically closed field, and let $N$ be a scheme which is affine and whose underlying space is connected, equipped with a morphism $f \colon N \to \operatorname{Spec} k$ that is smooth of relative dimension $h$ for a natural number $h$. Let $L$ be a relative group law for $f$: data assigning, to every $k$-scheme $t \colon T \to \operatorname{Spec} k$, a multiplication, a unit and an inversion on the set $\{\varphi : T \to N \mid \varphi \text{ followed by } f \text{ equals } t\}$ of $T$-points of $N$ over $k$, subject to associativity, both unit laws, the left inverse law, and naturality of the multiplication under composition with any $\psi \colon T' \to T$ satisfying $\psi$ followed by $t$ equals $t'$; assume further that all these multiplications are commutative. Let $m$ be a natural number whose image in $k$ is nonzero. Then the set of $k$-points of $N$ over $k$ (sections $\varphi \colon \operatorname{Spec} k \to N$ of $f$) that are $m$-torsion, that is, for which the $m$-fold iterate $(\cdots((1 \cdot \varphi) \cdot \varphi) \cdots) \cdot \varphi$ of the group law equals the unit, is finite, of cardinality at most $m^h$.
--
--   This is the torsion count for connected commutative affine (linear) algebraic groups of dimension $h$ over an algebraically closed field, one half of the input to Serre and Tate's lemma in the criterion of Néron–Ogg–Shafarevich, the other half being the count $m^{2\dim}$ for abelian varieties. It is used in the dichotomy [`GoodReductionJacobian.RelativeGroupLaw.isProper_or_natCard_isTorsionPoint_le_pow_sub_one`](thm.html#GoodReductionJacobian.RelativeGroupLaw.isProper_or_natCard_isTorsionPoint_le_pow_sub_one), which separates proper group laws from those with too few $m$-torsion points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_finite_and_natCard_isTorsionPoint_le_pow_of_isAffine.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.finite_and_natCard_isTorsionPoint_le_pow_of_isAffine
    (k : Type u) [Field k] [IsAlgClosed k] {N : Scheme.{u}} [IsAffine N] [ConnectedSpace N]
    (f : N ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    (h : ℕ) [SmoothOfRelativeDimension h f] (m : ℕ) (hm : (m : k) ≠ 0) :
    Finite {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f //
        L.IsTorsionPoint (𝟙 (Spec (CommRingCat.of k))) m x} ∧
      Nat.card {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f //
        L.IsTorsionPoint (𝟙 (Spec (CommRingCat.of k))) m x} ≤ m ^ h := by sorry
