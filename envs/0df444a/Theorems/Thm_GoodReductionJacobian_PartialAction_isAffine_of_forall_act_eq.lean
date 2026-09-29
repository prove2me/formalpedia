-- Prove2me | Theorems.Thm_GoodReductionJacobian_PartialAction_isAffine_of_forall_act_eq
-- name    : GoodReductionJacobian.PartialAction.isAffine_of_forall_act_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/30f14724-cadc-567d-8435-ce5364815282
-- title:
--   Rosenlicht's fixed-point criterion for affineness of G
-- statement:
--   Let $k$ be an algebraically closed field, $G$ a scheme whose underlying space is connected, and $f\colon G \to \operatorname{Spec} k$ a separated, quasi-compact, smooth morphism, equipped with a relative group law $L$: for every $k$-scheme $t\colon T \to \operatorname{Spec} k$ a multiplication, unit and inverse on the set of morphisms $T \to G$ over $t$, satisfying associativity, the unit laws and left inverse, with multiplication natural in $T$. Let $p\colon P \to \operatorname{Spec} k$ be separated and locally of finite type with $P$ integral, let $V \subseteq G$ be a non-empty open subscheme and $\iota\colon V \to P$ an open immersion over $k$ (that is, $\iota$ followed by $p$ equals the inclusion of $V$ followed by $f$). Let $a$ be a partial action: a dense open $\mathrm{dom} \subseteq G \times_{\operatorname{Spec} k} P$ together with a morphism $\mathrm{dom} \to P$ over $P$'s structure morphism along the second projection; for $T$-points $\gamma$ of $G$ and $x$ of $P$ over the same $t$, $\gamma \cdot x$ is said to be defined when the range of the induced morphism $T \to G \times_{\operatorname{Spec} k} P$ lies in $\mathrm{dom}$, and then $\gamma \cdot x$ denotes the resulting $T$-point of $P$. Assume: the unit acts trivially wherever defined ($a.UnitActs\ L$); associativity in the form that whenever $\delta \cdot x$ and $\gamma \cdot (\delta \cdot x)$ are defined, $(\gamma\delta) \cdot x$ is defined and the two agree ($a.Assoc\ L$); and compatibility with left translation ($a.Compatible$): for $T$-points $v, w$ of $V$ over $k$ and $\gamma$ of $G$, if $w$ pushed into $G$ equals $\gamma$ times $v$ pushed into $G$, then $\gamma \cdot \iota(v)$ is defined and equals $\iota(w)$. Finally, let $P_0$ be a $k$-point of $P$ such that the unit acts at $P_0$ in the above sense, and suppose every $k$-point $\gamma$ of $G$ for which $\gamma \cdot P_0$ is defined satisfies $\gamma \cdot P_0 = P_0$. Then $G$ is affine.
--
--   This is Rosenlicht's criterion: a connected smooth algebraic group acting birationally on an integral scheme containing a non-empty open subset of the group, and fixing a rational point wherever the action at that point is defined, must be affine. It is used in the form [`GoodReductionJacobian.PartialAction.isAffine_of_forall_exists_defined_act_eq`](thm.html#GoodReductionJacobian.PartialAction.isAffine_of_forall_exists_defined_act_eq), where the definedness hypothesis on the unit is supplied from a weaker global assumption.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_PartialAction_isAffine_of_forall_act_eq.lean

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

theorem GoodReductionJacobian.PartialAction.isAffine_of_forall_act_eq
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [IsSeparated p] [LocallyOfFiniteType p] [IsIntegral P]
    (V : G.Opens) [Nonempty (V : Scheme.{u})] (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι]
    (hι : ι ≫ p = V.ι ≫ f)
    (a : PartialAction k f p) (hu : a.UnitActs L) (ha : a.Assoc L) (hc : a.Compatible L V ι hι)
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p)
    (he : a.Defined (L.one (𝟙 (Spec (CommRingCat.of k)))) P₀)
    (hfix : ∀ (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hd : a.Defined γ P₀),
      a.act γ P₀ hd = P₀) :
    IsAffine G := by sorry
