-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_eq_of_one_comp_eq_one_comp_of_isPullback_of_comp_eq_comp_of_isNilpotent
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.eq_of_one_comp_eq_one_comp_of_isPullback_of_comp_eq_comp_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/3941e9c7-3b41-5bd5-a0b6-1b39cba7552b
-- title:
--   Rigidity of morphisms of abelian schemes along nilpotent base changes
-- statement:
--   Let $R$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} R$ a morphism satisfying `AbelianSchemePropertyBundle`, that is: $f$ is smooth, proper, each fibre $f^{-1}(s)$ over a point $s$ of $\operatorname{Spec} R$ is connected (as a topological space, and nonempty), and $f$ admits a relative group law. Let $L$ be such a relative group law: a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $A$-valued points over each $t : T \to \operatorname{Spec} R$, with associativity, two-sided unit, left inverses, and compatibility of multiplication with precomposition in $T$. Let $\varphi, \psi : A \to A$ be morphisms over $\operatorname{Spec} R$, i.e. $\varphi \circ f = f$ and $\psi \circ f = f$, which agree after composition with the unit section $\varepsilon := L.\mathrm{one}(\mathbf{1}_{\operatorname{Spec} R}) : \operatorname{Spec} R \to A$, so $\varepsilon$ followed by $\varphi$ equals $\varepsilon$ followed by $\psi$. Let $q : R \to R_0$ be a surjective ring homomorphism every element of whose kernel is nilpotent, and let $\pi : A_0 \to A$, $f_0 : A_0 \to \operatorname{Spec} R_0$ form a cartesian square with $f$ and $\operatorname{Spec}(q)$. If $\pi$ followed by $\varphi$ equals $\pi$ followed by $\psi$, then $\varphi = \psi$.
--
--   This is the formal unramifiedness of the scheme of morphisms of an abelian scheme under a nilpotent thickening of the base: two morphisms over the base agreeing on the unit section and after reduction coincide. It is used in the construction of quaternionic multiplication structures on polarised abelian schemes, via [`AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.formallyUnramified_of_represents`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.formallyUnramified_of_represents).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_eq_of_one_comp_eq_one_comp_of_isPullback_of_comp_eq_comp_of_isNilpotent.lean

import Mathlib
import Definitions.Def_JacJ1Iface

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.eq_of_one_comp_eq_one_comp_of_isPullback_of_comp_eq_comp_of_isNilpotent
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (hA : AbelianSchemePropertyBundle R f) (L : RelativeGroupLaw R f)
    (φ ψ : A ⟶ A) (hφ : φ ≫ f = f) (hψ : ψ ≫ f = f)
    (hone : (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ φ = (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ ψ)
    {R₀ : Type u} [CommRing R₀] (q : R →+* R₀) (hq : Function.Surjective q)
    (hnil : ∀ r : R, q r = 0 → IsNilpotent r)
    {A₀ : Scheme.{u}} {f₀ : A₀ ⟶ Spec (CommRingCat.of R₀)} (π : A₀ ⟶ A)
    (hπ : IsPullback π f₀ f (Spec.map (CommRingCat.ofHom q)))
    (h : π ≫ φ = π ≫ ψ) :
    φ = ψ := by sorry
