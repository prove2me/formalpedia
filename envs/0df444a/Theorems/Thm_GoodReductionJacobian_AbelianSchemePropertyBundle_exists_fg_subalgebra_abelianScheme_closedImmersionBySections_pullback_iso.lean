-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_fg_subalgebra_abelianScheme_closedImmersionBySections_pullback_iso
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_fg_subalgebra_abelianScheme_closedImmersionBySections_pullback_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/7c2f52f0-1154-5e82-8864-654dd42eb25a
-- title:
--   Noetherian approximation of an abelian scheme with very ample bundle
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$ a morphism equipped with: a relative group law $L$ on $f$, i.e. a multiplication, unit and inverse on $T$-points of $A$ over $\operatorname{Spec} S$, for all schemes $T$, satisfying the group axioms and natural in $T$; the bundle `AbelianSchemePropertyBundle S f`, asserting that $f$ is smooth and proper, that each fibre $f^{-1}(s)$ of the underlying map of spaces is connected (and nonempty), and that some relative group law on $f$ exists; and a module $\mathcal L$ on $A$ which is invertible (every point of $A$ has an open neighbourhood $U$ on which the pullback of $\mathcal L$ along $U \hookrightarrow A$ is isomorphic to the unit module) and satisfies `ClosedImmersionBySections` relative to $f$, i.e. for some $N$ there are $N+1$ global sections of $\mathcal L$ framing it on the preimages of the standard basic opens, inducing a morphism $A \to \operatorname{Proj}$ of the polynomial algebra in $N+1$ variables over $S$ which lies over $f$ and is a closed immersion. Then there exist a finitely generated $\mathbb Z$-subalgebra $S_0 \subseteq S$, a scheme $A_0$ with $f_0 : A_0 \to \operatorname{Spec} S_0$, a relative group law $L_0$ on $f_0$, the bundle `AbelianSchemePropertyBundle S₀ f₀`, the property `GeometricallyConnected f₀`, a module $\mathcal L_0$ on $A_0$ that is invertible and satisfies `ClosedImmersionBySections` relative to $f_0$, and a morphism $g_A : A \to A_0$ making the square with $f$, $f_0$ and $\operatorname{Spec}(S_0 \to S)$ cartesian, such that: commutativity of $L$ implies commutativity of $L_0$; $g_A$ is multiplicative on points, in that for every scheme $T$, every $t : T \to \operatorname{Spec} S$ and all $T$-points $x, y$ of $A$ over $t$, the point $L(x,y)$ followed by $g_A$ equals $L_0$ applied to $x$ followed by $g_A$ and $y$ followed by $g_A$, taken over the composite of $t$ with $\operatorname{Spec}(S_0 \to S)$; and the pullback of $\mathcal L_0$ along $g_A$ is isomorphic to $\mathcal L$.
--
--   This is the spreading-out (noetherian approximation) step for the pair consisting of an abelian scheme over an arbitrary affine base and a relatively very ample invertible module: everything descends to a finitely generated, hence noetherian, $\mathbb Z$-subalgebra of the base, compatibly with the group law and the polarising bundle. It is used to transfer cohomology-and-base-change statements about the global sections of such a module — finiteness and projectivity, and the comparison of sections with a tensor product along base change — from the noetherian situation to a general base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_fg_subalgebra_abelianScheme_closedImmersionBySections_pullback_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_fg_subalgebra_abelianScheme_closedImmersionBySections_pullback_iso
    {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (𝓛 : A.Modules) (hinv : Scheme.Modules.IsInvertible 𝓛) (hva : Scheme.Modules.ClosedImmersionBySections 𝓛 f) :
    ∃ (S₀ : Subalgebra ℤ S) (_ : S₀.FG)
      (A₀ : Scheme.{u}) (f₀ : A₀ ⟶ Spec (CommRingCat.of ↥S₀)) (L₀ : RelativeGroupLaw ↥S₀ f₀)
      (_ : AbelianSchemePropertyBundle ↥S₀ f₀) (_ : GeometricallyConnected f₀)
      (𝓛₀ : A₀.Modules) (_ : Scheme.Modules.IsInvertible 𝓛₀) (_ : Scheme.Modules.ClosedImmersionBySections 𝓛₀ f₀)
      (gA : A ⟶ A₀) (hg : IsPullback gA f f₀ (Spec.map (CommRingCat.ofHom (algebraMap ↥S₀ S)))),
      (L.IsCommutative → L₀.IsCommutative) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t f),
        (L.mul t x y).1 ≫ gA =
          (L₀.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥S₀ S)))
            ⟨x.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1) ∧
      Nonempty ((Scheme.Modules.pullback gA).obj 𝓛₀ ≅ 𝓛) := by sorry
