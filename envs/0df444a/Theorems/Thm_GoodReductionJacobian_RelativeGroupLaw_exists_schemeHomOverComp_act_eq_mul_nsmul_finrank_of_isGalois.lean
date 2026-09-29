-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_act_eq_mul_nsmul_finrank_of_isGalois
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_schemeHomOverComp_act_eq_mul_nsmul_finrank_of_isGalois
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/4e5eee02-20cd-56b6-bbb1-48537f003939
-- title:
--   Rosenlicht's torsor lemma in functor-of-points form
-- statement:
--   Let $K$ be a field, let $A$ be a $K$-scheme with structure morphism $f_A \colon A \to \operatorname{Spec} K$ which is separated and locally of finite type, and let $L_A$ be a relative group law on $f_A$: a functorial group structure assigning to each $K$-scheme $t \colon T \to \operatorname{Spec} K$ a multiplication, unit and inverse on the set of $T$-points $\{\varphi \colon T \to A \mid \varphi \circ f_A = t\}$, satisfying associativity, the unit laws, left inverses, and compatibility with precomposition along any $\psi \colon T' \to T$ with $\psi$ followed by $t$ equal to $t'$; assume $L_A$ is commutative, i.e. its multiplication on every such set of points is commutative. Let $g \colon V \to \operatorname{Spec} K$ be a further $K$-scheme, and let $\mathrm{act}$ assign to each $K$-scheme $t$ a map sending a $T$-point $a$ of $A$ and a $T$-point $v$ of $V$ to a $T$-point $\mathrm{act}\,t\,a\,v$ of $V$, subject to: compatibility with precomposition along any $\psi$ over $K$ (`act_natural`), the action law $\mathrm{act}\,t\,(a\cdot b)\,v = \mathrm{act}\,t\,a\,(\mathrm{act}\,t\,b\,v)$ (`act_mul`), and simple transitivity: for all $T$-points $v, w$ of $V$ there is a unique $T$-point $a$ of $A$ with $\mathrm{act}\,t\,a\,v = w$ (`act_torsor`). Let $K'/K$ be a finite Galois extension and let $P \colon \operatorname{Spec} K' \to V$ be a morphism with $P$ followed by $g$ equal to $\operatorname{Spec}$ of the structure map $K \to K'$. Then there exists a morphism $\varphi \colon V \to A$ with $\varphi$ followed by $f_A$ equal to $g$ such that for every $K$-scheme $t \colon T \to \operatorname{Spec} K$, every $T$-point $a$ of $A$ and every $T$-point $v$ of $V$, the composite $(\mathrm{act}\,t\,a\,v)$ followed by $\varphi$ equals the product of $v$ followed by $\varphi$ with the $n$-fold power of $a$ for $n = [K' : K]$, where the power is the iterated product $\mathrm{nsmul}$ formed from the unit by repeated multiplication by $a$.
--
--   This is Rosenlicht's lemma on torsors under a commutative algebraic group: a torsor with a point rational over a finite Galois extension of degree $n$ admits a morphism to the group converting translation by $a$ into translation by $a^{n}$, here phrased entirely in terms of functorial points. It is used, together with Galois descent of morphisms into a separated target locally of finite type, in the step showing that over an algebraically closed field such a torsor is trivialised, which in turn feeds the treatment of Néron models and Jacobians of curves with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_act_eq_mul_nsmul_finrank_of_isGalois.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_schemeHomOverComp_act_eq_mul_nsmul_finrank_of_isGalois
    (K : Type u) [Field K] {A : Scheme.{u}} (fA : A ⟶ Spec (CommRingCat.of K))
    [IsSeparated fA] [LocallyOfFiniteType fA]
    (LA : RelativeGroupLaw K fA) (hc : LA.IsCommutative)
    {V : Scheme.{u}} (g : V ⟶ Spec (CommRingCat.of K))
    (act : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)),
      SchemeHomOver t fA → SchemeHomOver t g → SchemeHomOver t g)
    (act_natural : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
      (t' : T' ⟶ Spec (CommRingCat.of K)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
      (a : SchemeHomOver t fA) (v : SchemeHomOver t g),
      GoodReductionJacobian.schemeHomOverComp ψ hψ (act t a v) =
        act t' (GoodReductionJacobian.schemeHomOverComp ψ hψ a)
          (GoodReductionJacobian.schemeHomOverComp ψ hψ v))
    (act_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
      (a b : SchemeHomOver t fA) (v : SchemeHomOver t g),
      act t (LA.mul t a b) v = act t a (act t b v))
    (act_torsor : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (v w : SchemeHomOver t g),
      ∃! a : SchemeHomOver t fA, act t a v = w)
    (K' : Type u) [Field K'] [Algebra K K'] [FiniteDimensional K K'] [IsGalois K K']
    (P : Spec (CommRingCat.of K') ⟶ V) (hP : P ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K K'))) :
    ∃ φ : SchemeHomOver g fA,
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (a : SchemeHomOver t fA)
        (v : SchemeHomOver t g),
        NeronModelInfra.schemeHomOverComp (act t a v) φ =
          LA.mul t (NeronModelInfra.schemeHomOverComp v φ) (LA.nsmul t (Module.finrank K K') a) := by sorry
