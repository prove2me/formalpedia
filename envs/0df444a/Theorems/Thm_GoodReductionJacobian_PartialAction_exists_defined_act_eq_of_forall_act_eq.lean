-- Prove2me | Theorems.Thm_GoodReductionJacobian_PartialAction_exists_defined_act_eq_of_forall_act_eq
-- name    : GoodReductionJacobian.PartialAction.exists_defined_act_eq_of_forall_act_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/d9223771-4fef-562d-b674-99e206cc2a9d
-- title:
--   Pointwise fixed k-point of a partial group action is universally fixed
-- statement:
--   Let $k$ be an algebraically closed field and let $f \colon G \to \operatorname{Spec} k$ be separated, quasi-compact and smooth with $G$ connected, equipped with a `RelativeGroupLaw` $L$: a group structure (multiplication, unit, inverse, with associativity, unit and inverse laws) on the sets $\{\varphi \colon T \to G \mid \varphi \circ f = t\}$ of $T$-points over $k$, the multiplication being compatible with base change $T' \to T$. Let $p \colon P \to \operatorname{Spec} k$ be separated and locally of finite type, and let $a$ be a `PartialAction`: a dense open subscheme $\mathrm{dom} \subseteq G \times_k P$ together with a morphism $\mathrm{hom} \colon \mathrm{dom} \to P$ over $k$. Say $\gamma \cdot x$ is defined, for $T$-points $\gamma$ of $G$ and $x$ of $P$, when the induced map $T \to G \times_k P$ has set-theoretic image inside $\mathrm{dom}$, and then $\gamma \cdot x$ denotes the $T$-point obtained by composing the lift $T \to \mathrm{dom}$ with $\mathrm{hom}$. Assume $a$ is associative relative to $L$: for all $T$-points, if $\delta \cdot x$ and $\gamma \cdot (\delta \cdot x)$ are defined then $(\gamma\delta) \cdot x$ is defined and equals $\gamma \cdot (\delta \cdot x)$. Let $P_0$ be a section of $p$ over $\operatorname{Spec} k$ such that $e \cdot P_0$ is defined, and assume every section $\gamma$ of $f$ over $\operatorname{Spec} k$ with $\gamma \cdot P_0$ defined satisfies $\gamma \cdot P_0 = P_0$. Then for every $k$-scheme $t \colon T \to \operatorname{Spec} k$ and every $T$-point $\gamma$ of $G$, the product $\gamma \cdot (t \circ P_0)$ is defined and equals $t \circ P_0$, the base change of $P_0$ to a $T$-point of $P$.
--
--   This is the scheme-theoretic form of Rosenlicht's observation that a rational point fixed by all rational points of a connected group at which the partial action is defined is fixed by the whole group, functorially in the test scheme; it rests on the fact that a dense open subset of a connected smooth group generates it. It is used in the study of partial actions on non-proper targets, in [`GoodReductionJacobian.PartialAction.isAffine_of_forall_act_eq`](thm.html#GoodReductionJacobian.PartialAction.isAffine_of_forall_act_eq) and in [`GoodReductionJacobian.RelativeGroupLaw.isAffine_or_exists_isClosedImmersion_lt_of_not_isProper`](thm.html#GoodReductionJacobian.RelativeGroupLaw.isAffine_or_exists_isClosedImmersion_lt_of_not_isProper).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_PartialAction_exists_defined_act_eq_of_forall_act_eq.lean

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

theorem GoodReductionJacobian.PartialAction.exists_defined_act_eq_of_forall_act_eq
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [IsSeparated p] [LocallyOfFiniteType p]
    (a : PartialAction k f p) (ha : a.Assoc L)
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p)
    (he : a.Defined (L.one (𝟙 (Spec (CommRingCat.of k)))) P₀)
    (hfix : ∀ (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hd : a.Defined γ P₀),
      a.act γ P₀ hd = P₀)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (γ : SchemeHomOver t f) :
    ∃ hd : a.Defined γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀),
      a.act γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀) hd =
        GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀ := by sorry
