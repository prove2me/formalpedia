-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_eq_schemeHomOverId_of_schemeHomOverNpow_eq_of_forall_isTorsionPoint_of_isUnit_of_three_le
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.eq_schemeHomOverId_of_schemeHomOverNpow_eq_of_forall_isTorsionPoint_of_isUnit_of_three_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/af942ebb-7ceb-5a93-bb16-6e0a2316b18f
-- title:
--   Rigidity: finite-order endomorphism fixing n-torsion is the identity
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} R$ a morphism satisfying the project's bundle `AbelianSchemePropertyBundle R f`, i.e. $f$ is smooth and proper, the fibre $f^{-1}(s)$ over each point $s$ of $\operatorname{Spec} R$ is connected, and $f$ admits at least one relative group law. Let $L$ be a relative group law on $f$: a group structure (multiplication, unit, inverse, with associativity, unit and inverse laws) on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $t$, compatible with composition in $T$. Let $n \ge 3$ be a natural number whose image in $R$ is a unit, and let $\sigma : A \to A$ satisfy $\sigma \circ f = f$, be a homomorphism for $L$ on $T$-points for every $R$-scheme $T$ (i.e. $L.\mathrm{mul}\,t\,x\,y$ composed with $\sigma$ equals the product of $x \circ \sigma$ and $y \circ \sigma$), have $\sigma^{m} = \mathrm{id}$ as an iterated composite for some $m \ne 0$, and fix the $n$-torsion of every geometric point: for every algebraically closed field $k$ (in the same universe), every $\iota : \operatorname{Spec} k \to \operatorname{Spec} R$ and every point $x$ of $A$ over $\iota$ with $n \cdot x$ (the $n$-fold $L$-sum) equal to the unit, $x \circ \sigma = x$. Then $\sigma$ is the identity of $A$, as an element of the set of endomorphisms over $f$.
--
--   This is Serre's rigidity lemma over an arbitrary base: for $n \ge 3$ invertible on the base, a finite-order endomorphism of an abelian scheme which is additive on points and induces the identity on $n$-torsion of all geometric points is the identity; it is what makes moduli problems for abelian schemes with level-$n$ structure rigid. It is used in the project to prove uniqueness and finiteness statements for morphisms of polarised abelian schemes, notably [`AlgebraicGeometry.PolarisedAbelianScheme.eq_of_isPullback_of_isPullback_of_three_le`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.eq_of_isPullback_of_isPullback_of_three_le) and its variants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_eq_schemeHomOverId_of_schemeHomOverNpow_eq_of_forall_isTorsionPoint_of_isUnit_of_three_le.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.eq_schemeHomOverId_of_schemeHomOverNpow_eq_of_forall_isTorsionPoint_of_isUnit_of_three_le
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (hA : AbelianSchemePropertyBundle R f) (L : RelativeGroupLaw R f)
    (n : ℕ) (hn3 : 3 ≤ n) (hn : IsUnit ((n : ℕ) : R)) (σ : SchemeHomOver f f)
    (hσ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) σ =
        L.mul t (NeronModelInfra.schemeHomOverComp x σ) (NeronModelInfra.schemeHomOverComp y σ))
    (m : ℕ) (hm : m ≠ 0) (hord : NeronModelInfra.schemeHomOverNpow σ m = NeronModelInfra.schemeHomOverId f)
    (hfix : ∀ (k : Type u) [Field k] [IsAlgClosed k] (ι : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (x : SchemeHomOver ι f), L.IsTorsionPoint ι n x → NeronModelInfra.schemeHomOverComp x σ = x) :
    σ = NeronModelInfra.schemeHomOverId f := by sorry
