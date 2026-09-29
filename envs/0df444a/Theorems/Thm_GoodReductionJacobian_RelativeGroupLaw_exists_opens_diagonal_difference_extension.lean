-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_opens_diagonal_difference_extension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/d0d2d066-23b7-5d4e-b52f-08a17b109d13
-- title:
--   Difference map extends over the diagonal (Weil extension, step 1)
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain), let $A$ and $T$ be schemes and $f\colon A\to\operatorname{Spec}R$ a morphism equipped with a relative group law $G$, i.e. a group structure on the sets $\{\varphi\colon T'\to A \mid \varphi\text{ followed by }f = t'\}$ of $R$-morphisms for all $t'\colon T'\to\operatorname{Spec}R$, with multiplication, unit and inverse compatible with precomposition along $R$-morphisms; assume $f$ smooth and separated. Let $t\colon T\to\operatorname{Spec}R$ be smooth, and let $V\subseteq T$ be an open subscheme such that every $x\in T$ with $t(x)$ different from the closed point of $\operatorname{Spec}R$ lies in $V$, and such that every irreducible component $Z$ of the subspace $\{x\in T \mid t(x)=\text{closed point}\}$ contains a point lying in $V$. Let $v\colon V\to A$ satisfy $v$ followed by $f$ equals the inclusion $V\hookrightarrow T$ followed by $t$. Then there exist an open $W\subseteq T\times_{\operatorname{Spec}R}T$ and a morphism $d\colon W\to A$ with $d$ followed by $f$ equal to $W\hookrightarrow T\times_R T$ followed by the first projection and then $t$, such that every point in the image of the diagonal $T\to T\times_R T$ lies in $W$, and such that for every scheme $S$ and all morphisms $a\colon S\to W$, $b,c\colon S\to V$ with $a$ followed by $W\hookrightarrow T\times_RT$ and the first (resp. second) projection equal to $b$ (resp. $c$) followed by $V\hookrightarrow T$, the $G$-product of $a$ followed by $d$ with $c$ followed by $v$ equals $b$ followed by $v$, as $R$-morphisms $S\to A$ over $a$ followed by $W\hookrightarrow T\times_RT$, the first projection and $t$.
--
--   This is the first step of Weil's extension theorem for rational maps into smooth separated group schemes over a discrete valuation ring: the difference map $(y,z)\mapsto v(y)v(z)^{-1}$, a priori defined on $V\times_R V$, extends to a neighbourhood of the whole diagonal of $T\times_R T$. It strengthens the companion statement, in which the open $W$ is only known to contain the points whose two projections both lie in $V$, and it feeds into the extension results for abelian schemes and the construction of descent data for relative group laws.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_opens_diagonal_difference_extension
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) [Smooth f] [IsSeparated f]
    (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t]
    (V : T.Opens) (hVη : ∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V)
    (hVs : ∀ Z ∈ irreducibleComponents {x : T // t.base x = IsLocalRing.closedPoint R}, ∃ x ∈ Z, x.1 ∈ V)
    (v : SchemeHomOver (V.ι ≫ t) f) :
    ∃ (W : (pullback t t).Opens) (d : SchemeHomOver (W.ι ≫ pullback.fst t t ≫ t) f),
      (∀ x : T, (pullback.diagonal t).base x ∈ W) ∧
      (∀ (S : Scheme.{u}) (a : S ⟶ ↑W) (b c : S ⟶ ↑V)
        (hb : a ≫ W.ι ≫ pullback.fst t t = b ≫ V.ι) (hc : a ≫ W.ι ≫ pullback.snd t t = c ≫ V.ι),
        G.mul (a ≫ W.ι ≫ pullback.fst t t ≫ t)
            ⟨a ≫ d.1, by rw [Category.assoc, d.2]⟩
            ⟨c ≫ v.1, by rw [Category.assoc, v.2, ← Category.assoc, ← hc, Category.assoc, Category.assoc,
              ← pullback.condition]⟩ =
          ⟨b ≫ v.1, by rw [Category.assoc, v.2, ← Category.assoc, ← hb, Category.assoc, Category.assoc]⟩) := by sorry
