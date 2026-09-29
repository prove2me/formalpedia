-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension
-- name    : GoodReductionJacobian.RelativeGroupLaw.hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/19d05ff1-ddab-581c-a5ce-eb890709206c
-- title:
--   Smooth relative dimension d forces p-divisible dimension d
-- statement:
--   Let $R$ be a commutative local ring, $J$ a scheme with a morphism $f \colon J \to \operatorname{Spec} R$, and $L$ a relative group law for $f$ in the sense of `RelativeGroupLaw`: for each $t \colon T \to \operatorname{Spec} R$ a multiplication, unit and inverse on the set $\{\varphi \colon T \to J \mid \varphi \text{ followed by } f = t\}$ of sections over $t$, satisfying associativity, the two unit laws and left invertibility, together with compatibility of the multiplication with base change along any $\psi$ over $\operatorname{Spec} R$. Assume $f$ is smooth of relative dimension $d$. Let $p, h$ be natural numbers and let $G$ be a $p$-divisible group over $R$ of height $h$ in the sense of [`PDivisibleGroup`](def/PDivisibleGroup_Basic.html#L199): levels `G.level v` that are finite free cocommutative $R$-Hopf algebras of rank $p^{vh}$, with surjective coalgebra transition maps whose kernels are the prescribed torsion ideals. Assume given, for every $v$ and every commutative $R$-algebra $T$, a bijection $e_{v,T}$ from $G$'s $T$-points at level $v$, i.e. $\operatorname{Hom}_{R\text{-alg}}(G.\mathrm{level}\,v, T)$ with the convolution product, onto the set of sections of $f$ over $\operatorname{Spec} T \to \operatorname{Spec} R$ that are killed by $p^v$ for the group law $L$, such that $e_{v,T}$ carries the convolution product to $L$'s multiplication, and such that for every $R$-algebra map $a \colon T \to T'$ the section underlying $e_{v,T'}$ of the transported point is $\operatorname{Spec}(a)$ followed by the section underlying $e_{v,T}(x)$. The conclusion is `G.HasDimension d`: for every $v$ the cotangent module $I_v/I_v^2$ of the augmentation ideal $I_v$ of `G.level v` admits an $R$-linear isomorphism onto $(R/(p^v))^{d}$.
--
--   This is the statement that the $p$-divisible group of a smooth commutative group scheme of relative dimension $d$ over a local ring has dimension $d$, the dimension being read off from the cotangent spaces of the finite levels along the unit section. It is used in the construction of the $p$-divisible group attached to $J$ together with the identification of its levels with the $p$-power torsion of $J$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_PDivisibleGroup_Dimension
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.hasDimension_of_point_equiv_torsionSubset_of_smoothOfRelativeDimension
    {R : Type} [CommRing R] [IsLocalRing R]
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (d : ℕ) [SmoothOfRelativeDimension d f]
    {p h : ℕ} (G : PDivisibleGroup R p h)
    (e : ∀ (v : ℕ) (T : Type) [CommRing T] [Algebra R T],
      G.Point T v ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap R T))) (p ^ v))
    (he_mul : ∀ (v : ℕ) (T : Type) [CommRing T] [Algebra R T] (x y : G.Point T v),
      ((e v T (x * y)).val : SchemeHomOver _ f) = L.mul _ (e v T x).val (e v T y).val)
    (he_nat : ∀ (v : ℕ) (T T' : Type) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
      (a : T →ₐ[R] T') (x : G.Point T v),
      ((e v T' (G.pointMap a v x)).val : SchemeHomOver _ f).1 =
        Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (e v T x).val.1) :
    G.HasDimension d := by sorry
