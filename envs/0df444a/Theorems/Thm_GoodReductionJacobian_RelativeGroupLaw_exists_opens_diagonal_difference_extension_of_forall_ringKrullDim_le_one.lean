-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/a1c49bb5-b08c-5e15-999a-492d51bde85e
-- title:
--   Difference map extends across the diagonal (Weil extension, step 1)
-- statement:
--   Let $k$ be a field, let $A$ and $T$ be schemes, let $f\colon A\to\operatorname{Spec} k$ be a separated morphism, and let $G$ be a relative group law on $f$: a group structure (multiplication, unit, inverse, with associativity, unit laws and left inverse) on the sets $\{\varphi\colon T'\to A \mid \varphi\circ f = t'\}$ of lifts of an arbitrary morphism $t'\colon T'\to\operatorname{Spec} k$ through $f$, compatible with precomposition by any morphism $\psi\colon T''\to T'$ over $\operatorname{Spec} k$. Let $t\colon T\to\operatorname{Spec} k$ be smooth, let $V\subseteq T$ be an open subscheme such that every point $x\in T$ with $\dim \mathcal{O}_{T,x}\le 1$ (Krull dimension of the stalk) lies in $V$, and let $v\colon V\to A$ satisfy $v\circ f = t|_V$. Then there are an open subscheme $W$ of $T\times_{\operatorname{Spec} k} T$ and a morphism $d\colon W\to A$ with $d\circ f$ equal to the structure morphism of $W$ (the inclusion of $W$ followed by the first projection and by $t$), such that: every point of $T$ is carried into $W$ by the underlying map of the diagonal $T\to T\times_{\operatorname{Spec} k}T$; and for every scheme $S$ and all morphisms $a\colon S\to W$, $b,c\colon S\to V$ with $a$ followed by $W\hookrightarrow T\times_{\operatorname{Spec} k}T$ and the first (resp. second) projection equal to $b$ (resp. $c$) followed by $V\hookrightarrow T$, the group law on lifts of the structure morphism of $S$ obtained from $a$ satisfies $(a\cdot d)\,(c\cdot v) = b\cdot v$, products denoting composites.
--
--   This is the first half of Weil's extension theorem for rational maps into group schemes over a field, in the reduction-to-the-diagonal form of Bosch–Lütkebohmert–Raynaud: the hypothesis on $V$ says that $T\setminus V$ has codimension at least $2$, and the conclusion extends the difference map $(y,z)\mapsto v(y)v(z)^{-1}$, a priori defined on $V\times_k V$, to an open neighbourhood of the diagonal. It is used in the construction of morphisms out of abelian schemes, via [`AlgebraicGeometry.exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle`](thm.html#AlgebraicGeometry.exists_comp_eq_of_isOpenImmersion_of_abelianSchemePropertyBundle).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_opens_diagonal_difference_extension_of_forall_ringKrullDim_le_one
    (k : Type u) [Field k]
    {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)} (G : RelativeGroupLaw k f) [IsSeparated f]
    (t : T ⟶ Spec (CommRingCat.of k)) [Smooth t]
    (V : T.Opens) (hV : ∀ x : T, ringKrullDim (T.presheaf.stalk x) ≤ 1 → x ∈ V)
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
