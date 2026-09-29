-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense
-- name    : GoodReductionJacobian.RelativeGroupLaw.exists_extension_of_diagonal_difference_extension_of_dense
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/04cdc28f-5196-5b45-af01-6defc63b1fc0
-- title:
--   Weil extension over a field: extension from a dense open
-- statement:
--   Let $k$ be a field, let $A$ and $T$ be schemes, and let $f \colon A \to \operatorname{Spec} k$ be a separated morphism carrying a relative group law $G$ over $k$, i.e. a group structure on the sets $\{\varphi \colon T' \to A \mid \varphi \text{ followed by } f = t'\}$ of points of $A$ over $k$-schemes $(T',t')$, with multiplication, unit and inverse satisfying associativity, the unit laws, left inversion, and compatibility with base change along any $\psi \colon T'' \to T'$ over $k$. Let $t \colon T \to \operatorname{Spec} k$ be smooth, let $V \subseteq T$ be an open subscheme whose underlying set is dense, and let $v \colon V \to A$ be a morphism with $v$ followed by $f$ equal to the restriction of $t$. Let $W \subseteq T \times_k T$ be an open subscheme and $d \colon W \to A$ a morphism over $k$, the structure morphism of $W$ being its inclusion followed by the first projection and $t$. Assume: (i) for every point $x$ of $T$ the image of $x$ under the diagonal $T \to T \times_k T$ lies in $W$; and (ii) for every scheme $S$ and all morphisms $a \colon S \to W$, $b, c \colon S \to V$ such that $a$ followed by $W \hookrightarrow T\times_k T$ and the first (respectively second) projection equals $b$ (respectively $c$) followed by $V \hookrightarrow T$, the identity $G.\mathrm{mul}(d \circ a, v \circ c) = v \circ b$ holds among points of $A$ over $S$. Then there exists a morphism $\varphi \colon T \to A$ with $\varphi$ followed by $f$ equal to $t$ whose restriction along $V \hookrightarrow T$ is $v$.
--
--   This is the second half of Weil's extension theorem for rational maps from a smooth scheme into a separated group scheme over a field, in the form used by Bosch–Lütkebohmert–Raynaud: once the "difference" morphism $d$ is defined on an open set containing the diagonal and recovers $v$ in the sense of (ii), the map $v$ extends over all of $T$ (no uniqueness is asserted here). It is invoked in the construction of morphisms out of open immersions in the abelian-scheme property bundle, which feeds the good-reduction input to the Jacobian side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension_of_dense.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_extension_of_diagonal_difference_extension_of_dense
    (k : Type u) [Field k]
    {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)} (G : RelativeGroupLaw k f) [IsSeparated f]
    (t : T ⟶ Spec (CommRingCat.of k)) [Smooth t]
    (V : T.Opens) (hV : Dense (V : Set T))
    (v : SchemeHomOver (V.ι ≫ t) f)
    (W : (pullback t t).Opens) (d : SchemeHomOver (W.ι ≫ pullback.fst t t ≫ t) f)
    (hd : (∀ x : T, (pullback.diagonal t).base x ∈ W) ∧
      (∀ (S : Scheme.{u}) (a : S ⟶ ↑W) (b c : S ⟶ ↑V)
        (hb : a ≫ W.ι ≫ pullback.fst t t = b ≫ V.ι) (hc : a ≫ W.ι ≫ pullback.snd t t = c ≫ V.ι),
        G.mul (a ≫ W.ι ≫ pullback.fst t t ≫ t)
            ⟨a ≫ d.1, by rw [Category.assoc, d.2]⟩
            ⟨c ≫ v.1, by rw [Category.assoc, v.2, ← Category.assoc, ← hc, Category.assoc, Category.assoc,
              ← pullback.condition]⟩ =
          ⟨b ≫ v.1, by rw [Category.assoc, v.2, ← Category.assoc, ← hb, Category.assoc, Category.assoc]⟩)) :
    ∃ φ : SchemeHomOver t f, V.ι ≫ φ.1 = v.1 := by sorry
