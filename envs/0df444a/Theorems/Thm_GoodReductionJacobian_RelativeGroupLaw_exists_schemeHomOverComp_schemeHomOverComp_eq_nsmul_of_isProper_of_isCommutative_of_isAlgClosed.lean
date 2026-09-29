-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_schemeHomOverComp_eq_nsmul_of_isProper_of_isCommutative_of_isAlgClosed
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_schemeHomOverComp_schemeHomOverComp_eq_nsmul_of_isProper_of_isCommutative_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/5fcefe3b-ff3d-5b3a-8888-548104998427
-- title:
--   Retraction up to isogeny onto an abelian subvariety
-- statement:
--   Let $k$ be an algebraically closed field and let $f \colon G \to \operatorname{Spec} k$ be a morphism of schemes that is separated, quasi-compact and smooth, with $G$ a connected topological space. Let $L$ be a relative group law on $f$ in the sense of `RelativeGroupLaw`: for every $k$-scheme $t \colon T \to \operatorname{Spec} k$ a multiplication, unit and inverse on the set $\mathrm{SchemeHomOver}\ t\ f = \{\varphi \colon T \to G \mid \varphi \circ f = t\}$ satisfying associativity, the unit laws and left inversion, and compatible with base change along any $\psi \colon T' \to T$ over $k$; assume $L$ is commutative, i.e. $L.\mathrm{mul}\ t\ x\ y = L.\mathrm{mul}\ t\ y\ x$ for all $t$, $x$, $y$. Let $j \colon A \to G$ be a closed immersion with $A$ connected, such that the composite $j$ followed by $f$ is proper and smooth, and let $L_A$ be a relative group law on that composite. Assume $j$ is a homomorphism on points: for every $t \colon T \to \operatorname{Spec} k$ and all $x, y \in \mathrm{SchemeHomOver}\ t\ (j \circ f)$, composing $L_A.\mathrm{mul}\ t\ x\ y$ with $j$ equals $L.\mathrm{mul}$ of the composites of $x$ and $y$ with $j$. The conclusion asserts the existence of a natural number $n > 0$ and a morphism $\pi \colon G \to A$ with $\pi$ followed by ($j$ followed by $f$) equal to $f$, such that (i) for every $t$ and all $x, y \in \mathrm{SchemeHomOver}\ t\ f$, composing $L.\mathrm{mul}\ t\ x\ y$ with $\pi$ equals $L_A.\mathrm{mul}\ t$ of the composites of $x$ and $y$ with $\pi$, and (ii) for every $t$ and every $x \in \mathrm{SchemeHomOver}\ t\ (j \circ f)$, composing $x$ first with $j$ and then with $\pi$ equals $\mathrm{nsmul}\ t\ n\ x$, the $n$-fold $L_A$-power of $x$ defined by recursion from the unit.
--
--   This is the first half of Rosenlicht's decomposition theorem for commutative algebraic groups: an abelian subvariety of a connected commutative algebraic group over an algebraically closed field is a retract up to isogeny, the retraction restricting to multiplication by $n$ on the subvariety. It is used in the construction of an almost-complement to such a subvariety, in [`GoodReductionJacobian.RelativeGroupLaw.exists_isClosedImmersion_surjective_mul_of_isProper_of_isCommutative`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_isClosedImmersion_surjective_mul_of_isProper_of_isCommutative).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_schemeHomOverComp_eq_nsmul_of_isProper_of_isCommutative_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_schemeHomOverComp_schemeHomOverComp_eq_nsmul_of_isProper_of_isCommutative_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [Smooth f] [ConnectedSpace G]
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative)
    {A : Scheme.{u}} (j : A ⟶ G) [IsClosedImmersion j] [ConnectedSpace A] [IsProper (j ≫ f)]
    [Smooth (j ≫ f)] (LA : RelativeGroupLaw k (j ≫ f))
    (hj : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (j ≫ f)),
      NeronModelInfra.schemeHomOverComp (LA.mul t x y) (⟨j, rfl⟩ : SchemeHomOver (j ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨j, rfl⟩ : SchemeHomOver (j ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨j, rfl⟩ : SchemeHomOver (j ≫ f) f))) :
    ∃ (n : ℕ) (π : SchemeHomOver f (j ≫ f)), 0 < n ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
        NeronModelInfra.schemeHomOverComp (L.mul t x y) π =
          LA.mul t (NeronModelInfra.schemeHomOverComp x π)
            (NeronModelInfra.schemeHomOverComp y π)) ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t (j ≫ f)),
        NeronModelInfra.schemeHomOverComp
            (NeronModelInfra.schemeHomOverComp x (⟨j, rfl⟩ : SchemeHomOver (j ≫ f) f)) π =
          LA.nsmul t n x := by sorry
