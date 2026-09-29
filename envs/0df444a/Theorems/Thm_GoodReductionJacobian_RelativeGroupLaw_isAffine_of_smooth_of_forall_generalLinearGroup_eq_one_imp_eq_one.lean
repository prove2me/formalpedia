-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isAffine_of_smooth_of_forall_generalLinearGroup_eq_one_imp_eq_one
-- name    : GoodReductionJacobian.RelativeGroupLaw.isAffine_of_smooth_of_forall_generalLinearGroup_eq_one_imp_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/401ee7f1-7be6-5396-9407-a0dccbf39dff
-- title:
--   Faithful d-dimensional representation implies affineness of G
-- statement:
--   Let $k$ be a field, $G$ a scheme and $f\colon G \to \operatorname{Spec} k$ a morphism that is locally of finite type, quasi-compact and smooth. For a scheme $T$ and a structure morphism $t\colon T \to \operatorname{Spec} k$, write $G(t)$ for the set `SchemeHomOver t f` of morphisms $\varphi\colon T \to G$ with $\varphi$ followed by $f$ equal to $t$. Let $L$ be a `RelativeGroupLaw` for $f$, i.e. operations $\mathrm{mul}$, $\mathrm{one}$, $\mathrm{inv}$ on each $G(t)$ satisfying associativity, both unit laws and left inverses, with $\mathrm{mul}$ natural under precomposition with any $\psi\colon T' \to T$ over $k$. Let $d \in \mathbb{N}$ and suppose given, for every $T$ and every $t$, a map $\rho_t\colon G(t) \to \mathrm{GL}_d(\Gamma(T,\mathcal{O}_T))$ such that: $\rho_t(L.\mathrm{mul}\,t\,x\,y) = \rho_t(x)\rho_t(y)$; for $\psi\colon T' \to T$ with $\psi$ followed by $t$ equal to $t'$, $\rho_{t'}(\psi \circ x)$ is the image of $\rho_t(x)$ under the entrywise map induced by $\psi^{*}$ on global sections; and $\rho_t(x) = 1$ forces $x = L.\mathrm{one}\,t$. Then $G$ is an affine scheme.
--
--   This is the non-trivial direction of the equivalence "linear $\Leftrightarrow$ affine" for algebraic groups over a field: a homomorphism of group functors $G \to \mathrm{GL}_d$ with trivial kernel on all test schemes is a monomorphism, hence a closed immersion for group schemes of finite type, exhibiting $G$ as a closed subscheme of the affine scheme $\mathrm{GL}_{d,k}$. It is used in the good-reduction analysis of Jacobians, where it is cited by [`GoodReductionJacobian.PartialAction.isAffine_of_forall_act_eq`](thm.html#GoodReductionJacobian.PartialAction.isAffine_of_forall_act_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isAffine_of_smooth_of_forall_generalLinearGroup_eq_one_imp_eq_one.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.isAffine_of_smooth_of_forall_generalLinearGroup_eq_one_imp_eq_one
    {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
    [LocallyOfFiniteType f] [QuasiCompact f] [Smooth f] (L : RelativeGroupLaw k f) (d : ℕ)
    (ρ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)),
      SchemeHomOver t f → GL (Fin d) Γ(T, ⊤))
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      ρ t (L.mul t x y) = ρ t x * ρ t y)
    (hnat : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
      (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f),
      ρ t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
        Matrix.GeneralLinearGroup.map ψ.appTop.hom (ρ t x))
    (hker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
      ρ t x = 1 → x = L.one t) :
    IsAffine G := by sorry
