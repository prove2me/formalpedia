-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_isGreatest_opens_difference_extension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/e7d1df8d-affd-5ef0-853a-bcb78b651173
-- title:
--   Largest open of definition of the difference map
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain with the discrete valuation ring structure), let $A$ and $T$ be schemes, and let $f \colon A \to \operatorname{Spec} R$ be a separated morphism carrying a relative group law $G$: a group structure on the set $\{\varphi \colon T' \to A \mid \varphi \text{ followed by } f = t'\}$ of $R$-morphisms to $A$, for every $R$-scheme $t' \colon T' \to \operatorname{Spec} R$, whose multiplication is natural in $T'$. Let $t \colon T \to \operatorname{Spec} R$ be smooth, let $V$ be an open subscheme of $T$ such that every $x \in T$ with $t(x)$ not the closed point of $R$ lies in $V$, and such that every irreducible component $Z$ of the fibre $\{x \in T \mid t(x) = \text{closed point}\}$ contains a point lying in $V$; let $v \colon V \to A$ be a morphism over $\operatorname{Spec} R$ (the structure morphism of $V$ being the inclusion followed by $t$). Then there are an open subscheme $W$ of $T \times_{\operatorname{Spec} R} T$ and a morphism $d \colon W \to A$ over $\operatorname{Spec} R$ (structure morphism: the inclusion followed by the first projection followed by $t$) such that: (i) every point $p$ of $T \times_R T$ both of whose projections lie in $V$ lies in $W$; (ii) for every scheme $S$ and morphisms $a \colon S \to W$, $b, c \colon S \to V$ with $a$ followed by $W \hookrightarrow T\times_R T$ and the first (resp. second) projection equal to $b$ (resp. $c$) followed by $V \hookrightarrow T$, the product in $G$ of $a \circ d$ and $c \circ v$ equals $b \circ v$ as $S$-points of $A$; and (iii) the pair $(W,d)$ is greatest with this extension property: for every open $W'$ of $T \times_R T$ with a morphism $d' \colon W' \to A$ over $\operatorname{Spec} R$ and every open $W_0 \le W \sqcap W'$ with $W' \subseteq \overline{W_0}$ on which the restrictions of $d$ and $d'$ agree, one has $W' \le W$, and for all $a' \colon S \to W'$, $a \colon S \to W$ agreeing after composition with the inclusions, $a' \circ d' = a \circ d$.
--
--   This is the domain-of-definition bookkeeping in Weil's extension theorem for rational maps into group schemes, as used in the construction of Néron models: $d$ is the difference map $(y,z) \mapsto v(y)v(z)^{-1}$, a rational map $T \times_R T \dashrightarrow A$ defined on the dense open $V \times_R V$, and $W$ is its maximal open domain of definition, available because $T$ is smooth over $R$ and $f$ is separated. It feeds into [`GoodReductionJacobian.RelativeGroupLaw.exists_opens_diagonal_difference_extension`](thm.html#GoodReductionJacobian.RelativeGroupLaw.exists_opens_diagonal_difference_extension), where the difference map is used near the diagonal to extend $v$ itself.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isGreatest_opens_difference_extension
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) [IsSeparated f]
    (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t]
    (V : T.Opens) (hVη : ∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V)
    (hVs : ∀ Z ∈ irreducibleComponents {x : T // t.base x = IsLocalRing.closedPoint R}, ∃ x ∈ Z, x.1 ∈ V)
    (v : SchemeHomOver (V.ι ≫ t) f) :
    ∃ (W : (pullback t t).Opens) (d : SchemeHomOver (W.ι ≫ pullback.fst t t ≫ t) f),
      (∀ p : ↑(pullback t t), (pullback.fst t t).base p ∈ V → (pullback.snd t t).base p ∈ V → p ∈ W) ∧
      (∀ (S : Scheme.{u}) (a : S ⟶ ↑W) (b c : S ⟶ ↑V)
        (hb : a ≫ W.ι ≫ pullback.fst t t = b ≫ V.ι) (hc : a ≫ W.ι ≫ pullback.snd t t = c ≫ V.ι),
        G.mul (a ≫ W.ι ≫ pullback.fst t t ≫ t)
            ⟨a ≫ d.1, by rw [Category.assoc, d.2]⟩
            ⟨c ≫ v.1, by rw [Category.assoc, v.2, ← Category.assoc, ← hc, Category.assoc, Category.assoc,
              ← pullback.condition]⟩ =
          ⟨b ≫ v.1, by rw [Category.assoc, v.2, ← Category.assoc, ← hb, Category.assoc, Category.assoc]⟩) ∧
      (∀ (W' : (pullback t t).Opens) (d' : SchemeHomOver (W'.ι ≫ pullback.fst t t ≫ t) f)
        (W₀ : (pullback t t).Opens) (h₀ : W₀ ≤ W ⊓ W'),
        ((W' : Set ↑(pullback t t)) ⊆ closure (W₀ : Set ↑(pullback t t))) →
        (pullback t t).homOfLE (h₀.trans inf_le_left) ≫ d.1 = (pullback t t).homOfLE (h₀.trans inf_le_right) ≫ d'.1 →
        W' ≤ W ∧ ∀ (S : Scheme.{u}) (a' : S ⟶ ↑W') (a : S ⟶ ↑W), a' ≫ W'.ι = a ≫ W.ι → a' ≫ d'.1 = a ≫ d.1) := by sorry
