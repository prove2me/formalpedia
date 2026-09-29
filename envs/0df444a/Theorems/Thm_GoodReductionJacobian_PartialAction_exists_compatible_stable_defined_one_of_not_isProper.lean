-- Prove2me | Theorems.Thm_GoodReductionJacobian_PartialAction_exists_compatible_stable_defined_one_of_not_isProper
-- name    : GoodReductionJacobian.PartialAction.exists_compatible_stable_defined_one_of_not_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/4dbd742e-163d-53d3-8954-de201e3f99aa
-- title:
--   Rational translation action with a small stable closed subset
-- statement:
--   Let $k$ be an algebraically closed field, $G$ a scheme and $f : G \to \operatorname{Spec} k$ a separated, quasi-compact morphism with $G$ connected and $f$ smooth of relative dimension $g$ for some natural number $g$, and let $L$ be a relative group law on $f$, that is, a functorial group structure (multiplication, unit, inverse, the group axioms, and naturality of multiplication under base change) on the sets $\{\varphi : T \to G \mid \varphi \circ f = t\}$ of sections over arbitrary $t : T \to \operatorname{Spec} k$. Assume $f$ is not proper. Then there exist an open subscheme $V \subseteq G$ with non-empty underlying scheme, a scheme $P$ with a separated, locally of finite type morphism $p : P \to \operatorname{Spec} k$ and $P$ integral, and an open immersion $\iota : V \to P$ over $k$ (i.e. $\iota$ followed by $p$ equals the inclusion $V \to G$ followed by $f$), together with a partial action $a$ of $G$ on $P$ — a dense open $\operatorname{dom} a \subseteq G \times_{k} P$ together with a morphism $\operatorname{dom} a \to P$ commuting with the structure morphisms to $\operatorname{Spec} k$ via the second projection — with the following properties. First, $a$ is compatible with left translation along $\iota$: for every $t : T \to \operatorname{Spec} k$, every section $\gamma$ of $f$ over $t$ and all sections $v, w$ of $V \to \operatorname{Spec} k$ over $t$ whose images in $G$ satisfy $w = \gamma \cdot v$ for $L$, the pair $(\gamma, v \circ \iota)$ factors through $\operatorname{dom} a$ and $a$ carries $v \circ \iota$ to $w \circ \iota$. Second, $a$ satisfies `UnitActs` for $L$ (the unit section acts as the identity wherever defined) and `Assoc` for $L$ (acting by $\delta$ and then by $\gamma$ is defined for $\gamma \cdot \delta$ and agrees with the action of $\gamma \cdot \delta$). Third, there is a closed subset $W \subseteq P$ stable under $a$ (if a point of $\operatorname{dom} a$ has second projection in $W$, its image under the action morphism lies in $W$) with $\dim W + 1 \le g$ for the topological Krull dimension, computed in $\mathrm{WithBot}\ \mathbb{N}_\infty$, and a section $P_0$ of $p$ over the identity of $\operatorname{Spec} k$, i.e. a $k$-point of $P$, whose image of the closed point lies in $W$ and at which the unit section of $L$ acts in the defined sense, namely the pair $(1, P_0) : \operatorname{Spec} k \to G \times_k P$ has range inside $\operatorname{dom} a$.
--
--   This is the geometric input, in Rosenlicht's style as arranged by Milne, for showing that a smooth connected group scheme over an algebraically closed field which is not proper admits a suitable small invariant closed subset in a partial compactification: a non-empty affine-like open of $G$ is completed to an integral model $P$ on which left translation becomes a rational action, and the boundary behaviour produces a stable closed $W$ of dimension at most $g - 1$ carrying a rational point at which the unit acts. It is used in the dichotomy [`GoodReductionJacobian.RelativeGroupLaw.isAffine_or_exists_isClosedImmersion_lt_of_not_isProper`](thm.html#GoodReductionJacobian.RelativeGroupLaw.isAffine_or_exists_isClosedImmersion_lt_of_not_isProper), where the bound on $\dim W$ drives the induction on dimension.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_PartialAction_exists_compatible_stable_defined_one_of_not_isProper.lean

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

theorem GoodReductionJacobian.PartialAction.exists_compatible_stable_defined_one_of_not_isProper
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G]
    (L : RelativeGroupLaw k f) (g : ℕ) [SmoothOfRelativeDimension g f] (hG : ¬ IsProper f) :
    ∃ (V : G.Opens) (_ : Nonempty (V : Scheme.{u})) (P : Scheme.{u}) (p : P ⟶ Spec (CommRingCat.of k))
      (_ : IsSeparated p) (_ : LocallyOfFiniteType p) (_ : IsIntegral P)
      (ι : (V : Scheme.{u}) ⟶ P) (_ : IsOpenImmersion ι) (hι : ι ≫ p = V.ι ≫ f)
      (a : PartialAction k f p), a.Compatible L V ι hι ∧ a.UnitActs L ∧ a.Assoc L ∧
      ∃ (W : Set ↥P), IsClosed W ∧ a.Stable W ∧ topologicalKrullDim ↥W + 1 ≤ (g : WithBot ℕ∞) ∧
        ∃ P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p,
          P₀.1 (IsLocalRing.closedPoint k) ∈ W ∧ a.Defined (L.one (𝟙 (Spec (CommRingCat.of k)))) P₀ := by sorry
