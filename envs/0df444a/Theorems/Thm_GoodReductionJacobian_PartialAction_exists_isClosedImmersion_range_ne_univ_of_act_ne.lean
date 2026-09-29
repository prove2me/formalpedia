-- Prove2me | Theorems.Thm_GoodReductionJacobian_PartialAction_exists_isClosedImmersion_range_ne_univ_of_act_ne
-- name    : GoodReductionJacobian.PartialAction.exists_isClosedImmersion_range_ne_univ_of_act_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/c3b8bec1-f3e7-516f-8a71-f89132282ae8
-- title:
--   Isotropy subgroup of a moved point in a low-dimensional stable closed set
-- statement:
--   Let $k$ be an algebraically closed field, $G$ a scheme with a separated, quasi-compact structure morphism $f\colon G\to\operatorname{Spec} k$ whose underlying space is connected, and let $L$ be a relative group law for $f$: a group structure, natural in the base, on the sets $\{\varphi\colon T\to G \mid \varphi\circ f=t\}$ of sections over each $k$-scheme $t\colon T\to\operatorname{Spec} k$. Assume $f$ is smooth of relative dimension $g$. Let $p\colon P\to\operatorname{Spec} k$ be separated and locally of finite type, and let $a$ be a partial action of $f$ on $p$: a dense open subscheme $\mathrm{dom}\subseteq G\times_k P$ together with a morphism $\mathrm{hom}\colon\mathrm{dom}\to P$ over $k$ compatible with the second projection. Assume the unit acts trivially wherever defined, and associativity in the form that whenever $\delta\cdot x$ and $\gamma\cdot(\delta\cdot x)$ are defined so is $(\gamma\delta)\cdot x$, with the same value. Let $W\subseteq P$ be closed with $\dim W+1\le g$ (topological Krull dimension, in $\mathrm{WithBot}\,\mathbb{N}\infty$) and stable: $\mathrm{hom}(z)\in W$ for every point $z$ of $\mathrm{dom}$ whose second projection lies in $W$. Let $P_0$ be a $k$-point of $P$ sending the closed point of $\operatorname{Spec} k$ into $W$, with $e\cdot P_0$ defined, and let $\gamma_0$ be a $k$-point of $G$ with $\gamma_0\cdot P_0$ defined and $\gamma_0\cdot P_0\ne P_0$. Then there are a scheme $H$, a morphism $i\colon H\to G$ and a relative group law $LH$ for $i$ followed by $f$ such that $i$ is a closed immersion; for all $T$, $t\colon T\to\operatorname{Spec} k$ and sections $x,y$ of $i\circ f$ over $t$, the image under $i$ of $LH$-product of $x$ and $y$ is the $L$-product of the images of $x$ and $y$ under $i$; the set-theoretic range of $i$ is not all of $G$; and the connected component, in $H$, of the image of the closed point of $\operatorname{Spec} k$ under the $LH$-identity $k$-point has topological Krull dimension at least $1$.
--
--   This is Rosenlicht's lemma on isotropy groups for a rational action: if a point of a stable closed subset of dimension smaller than $\dim G$ is moved by some rational point of $G$, its stabiliser is a proper closed subgroup scheme of $G$ whose identity component is positive-dimensional. It is used in the dichotomy [`GoodReductionJacobian.RelativeGroupLaw.isAffine_or_exists_isClosedImmersion_lt_of_not_isProper`](thm.html#GoodReductionJacobian.RelativeGroupLaw.isAffine_or_exists_isClosedImmersion_lt_of_not_isProper), part of the construction of Néron models for Jacobians of curves with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_PartialAction_exists_isClosedImmersion_range_ne_univ_of_act_ne.lean

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

theorem GoodReductionJacobian.PartialAction.exists_isClosedImmersion_range_ne_univ_of_act_ne
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G]
    (L : RelativeGroupLaw k f) (g : ℕ) [SmoothOfRelativeDimension g f]
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [IsSeparated p] [LocallyOfFiniteType p]
    (a : PartialAction k f p) (hu : a.UnitActs L) (ha : a.Assoc L)
    (W : Set ↥P) (hW : IsClosed W) (hWg : topologicalKrullDim ↥W + 1 ≤ (g : WithBot ℕ∞))
    (hst : a.Stable W)
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p)
    (hP₀ : P₀.1 (IsLocalRing.closedPoint k) ∈ W)
    (he : a.Defined (L.one (𝟙 (Spec (CommRingCat.of k)))) P₀)
    (γ₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hγ₀ : a.Defined γ₀ P₀)
    (hne : a.act γ₀ P₀ hγ₀ ≠ P₀) :
    ∃ (H : Scheme.{u}) (i : H ⟶ G) (LH : RelativeGroupLaw k (i ≫ f)),
      IsClosedImmersion i ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
        NeronModelInfra.schemeHomOverComp (LH.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
            (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) ∧
      Set.range i ≠ Set.univ ∧
      1 ≤ topologicalKrullDim
        ↥(connectedComponent ((LH.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint k))) := by sorry
