-- Prove2me | Theorems.Thm_GoodReductionJacobian_PartialAction_exists_generalLinearGroup_jet_of_forall_defined_act_eq
-- name    : GoodReductionJacobian.PartialAction.exists_generalLinearGroup_jet_of_forall_defined_act_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/d08166c1-f022-512e-bd1e-214888cf0d46
-- title:
--   Jet representations for a partial action fixing a rational point
-- statement:
--   Let $k$ be a field, let $f : G \to \operatorname{Spec} k$ be a separated, quasi-compact morphism of schemes, and let $L$ be a relative group law for $f$: a group structure on each set of morphisms $T \to G$ over $\operatorname{Spec} k$, natural in $T$. Let $p : P \to \operatorname{Spec} k$ be locally of finite type and let $a$ be a partial action of $f$ on $p$, that is, a dense open $U \subseteq G \times_{\operatorname{Spec} k} P$ together with a morphism $U \to P$ over $\operatorname{Spec} k$; write $\gamma \cdot x$ for the resulting $T$-point of $P$ whenever the pair $(\gamma, x)$ factors through $U$ ('defined'). Assume `a.UnitActs L` ($e \cdot x = x$ whenever defined) and `a.Assoc L` (if $\delta \cdot x$ and $\gamma \cdot (\delta \cdot x)$ are defined then so is $(\gamma\delta) \cdot x$, with the same value). Let $P_0$ be a section of $p$, i.e. a $k$-rational point of $P$, and assume that for every $T$, every $t : T \to \operatorname{Spec} k$ and every $T$-point $\gamma$ of $G$ over $t$, the pair of $\gamma$ with the point $t$ followed by $P_0$ is defined and is fixed by $\gamma$. Then there are natural numbers $d_n$ and, for each $n$, an assignment $\rho_n$ sending every $T$-point $x$ of $G$ over $t : T \to \operatorname{Spec} k$ to a matrix $\rho_n(t,x) \in \mathrm{GL}_{d_n}(\Gamma(T, \mathcal{O}_T))$, such that: (1) $\rho_n(t, xy) = \rho_n(t,x)\rho_n(t,y)$ for the group law $L$; (2) for $\psi : T' \to T$ with $\psi$ followed by $t$ equal to $t'$, $\rho_n(t', \psi \text{ followed by } x)$ is the entrywise image of $\rho_n(t,x)$ under the map $\psi^{*}$ on global sections; (3) $\rho_{n+1}(t,x) = 1$ implies $\rho_n(t,x) = 1$; and (4) for every morphism $j_n : \operatorname{Spec}\bigl(\mathcal{O}_{P,\,P_0(\mathfrak{c})}/\mathfrak{m}^n\bigr) \to P$, where $\mathfrak{c}$ is the closed point of $\operatorname{Spec} k$ and $j_n$ is $\operatorname{Spec}$ of the quotient map followed by the canonical morphism from the spectrum of the stalk, $\rho_n(t,x) = 1$ implies that the base change of $x$ along the first projection of the pullback of $t$ and $j_n \circ p$, paired with the $P$-point given by the second projection followed by $j_n$, is defined and is fixed by that base change of $x$.
--
--   This is the scheme-theoretic form of the classical construction, going back to Rosenlicht, of the finite-dimensional linear representations of a group on the jets (truncated local rings) of order $n$ at a rational point fixed by a rational action, together with the compatibility of the tower in $n$ and the statement that triviality of the $n$-th representation forces trivial action on $n$-jets. It is used in the proof that a scheme carrying such a partial action is affine ([`GoodReductionJacobian.PartialAction.isAffine_of_forall_act_eq`](thm.html#GoodReductionJacobian.PartialAction.isAffine_of_forall_act_eq)), a step in the construction of Néron models and the good reduction theory for Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_PartialAction_exists_generalLinearGroup_jet_of_forall_defined_act_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_PartialAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.PartialAction.exists_generalLinearGroup_jet_of_forall_defined_act_eq
    (k : Type u) [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (a : PartialAction k f p) (hu : a.UnitActs L) (ha : a.Assoc L)
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p)
    (hall : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (γ : SchemeHomOver t f),
      ∃ hd : a.Defined γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀),
        a.act γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀) hd =
          GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀) :
    ∃ (d : ℕ → ℕ)
      (ρ : ∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)),
        SchemeHomOver t f → GL (Fin (d n)) Γ(T, ⊤)),
      (∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
        ρ n t (L.mul t x y) = ρ n t x * ρ n t y) ∧
      (∀ (n : ℕ) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
        (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
        (x : SchemeHomOver t f),
        ρ n t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
          Matrix.GeneralLinearGroup.map ψ.appTop.hom (ρ n t x)) ∧
      (∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
        ρ (n + 1) t x = 1 → ρ n t x = 1) ∧
      (∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f)
        (jn : Spec (CommRingCat.of (P.presheaf.stalk (P₀.1.base (IsLocalRing.closedPoint k)) ⧸
            IsLocalRing.maximalIdeal (P.presheaf.stalk (P₀.1.base (IsLocalRing.closedPoint k))) ^ n))
            ⟶ P),
        jn = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ P.fromSpecStalk _ →
        ρ n t x = 1 →
        ∃ hd : a.Defined
            (GoodReductionJacobian.schemeHomOverComp (pullback.fst t (jn ≫ p)) rfl x :
              SchemeHomOver (pullback.fst t (jn ≫ p) ≫ t) f)
            (⟨pullback.snd t (jn ≫ p) ≫ jn, by rw [Category.assoc, pullback.condition]⟩ :
              SchemeHomOver (pullback.fst t (jn ≫ p) ≫ t) p),
          (a.act _ _ hd).1 = pullback.snd t (jn ≫ p) ≫ jn) := by sorry
