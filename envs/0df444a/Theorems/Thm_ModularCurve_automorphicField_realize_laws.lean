-- Prove2me | Theorems.Thm_ModularCurve_automorphicField_realize_laws
-- name    : ModularCurve.automorphicField_realize_laws
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/962fd07f-6722-545e-b2b8-03ca23eea799
-- title:
--   Realisation laws for the field of automorphic functions
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{GL}_2(\mathbb{R})$ all of whose elements have determinant $1$. Write $\mathcal{O}$ for [`ModularCurve.holRing`](def/ModularCurve_AutomorphicField.html#L13), the $\mathbb{C}$-subalgebra of all functions $\mathbb{H} \to \mathbb{C}$ that are holomorphic (`MDifferentiable` for the standard complex charts), and recall that [`ModularCurve.merRealize`](def/ModularCurve_AutomorphicField.html#L35) sends an element of $\mathrm{Frac}(\mathcal{O})$ to the function $z \mapsto a(z)/s(z)$ built from one chosen localisation representative $a/s$, while [`ModularCurve.automorphicField`](def/ModularCurve_AutomorphicField.html#L150) $\Gamma$ is the subfield of $\mathrm{Frac}(\mathcal{O})$ consisting of the quotients $g/h$ with $g,h$ modular forms of some common weight $k$ for $\Gamma$ and $h \neq 0$ as a function, realised through [`ModularCurve.automorphicField.realize`](def/ModularCurve_AutomorphicField.html#L193) by the same construction. The theorem asserts the conjunction of seven facts. First, for all $a,s \in \mathcal{O}$ with $s \neq 0$ and every $\tau \in \mathbb{H}$, one has $\mathrm{merRealize}(a/s)(z) = a(z)/s(z)$ for $z$ in a punctured neighbourhood of $\tau$ (eventually along $\mathcal{N}[\neq]\,\tau$). Second, for every $x$ in the automorphic field and every $\tau \in \mathbb{H}$, the function $z \mapsto \mathrm{realize}\,x(\mathrm{ofComplex}\,z)$ on $\mathbb{C}$ is meromorphic at $\tau$. Third and fourth, realisation is additive and multiplicative eventually along $\mathcal{N}[\neq]\,\tau$ at each $\tau$. Fifth, the realisation of the image of $c \in \mathbb{C}$ under the structure map equals the constant $c$ there. Sixth, two elements whose realisations agree on a punctured neighbourhood of every $\tau \in \mathbb{H}$ are equal. Seventh, for every $\gamma \in \Gamma$ and every $\tau$, $\mathrm{realize}\,x(\gamma \cdot z) = \mathrm{realize}\,x(z)$ for $z$ in a punctured neighbourhood of $\tau$.
--
--   These are the basic working properties of the field of automorphic functions for $\Gamma$ as a field of meromorphic functions on the upper half plane: the realisation map is a $\mathbb{C}$-algebra homomorphism onto germs away from polar sets, is injective on germs, and lands in $\Gamma$-invariant functions. No discreteness or compactness assumption on $\Gamma$ enters. The statement is used in the construction of points and of functions on uniformised modular curves, in [`ModularCurve.UniformizedHeckeCurve.exists_of_isCompact_of_discrete`](thm.html#ModularCurve.UniformizedHeckeCurve.exists_of_isCompact_of_discrete), [`ModularCurve.exists_pt_eq_of_isCompact`](thm.html#ModularCurve.exists_pt_eq_of_isCompact) and [`ModularCurve.exists_realize_eventuallyEq_of_isCompact`](thm.html#ModularCurve.exists_realize_eventuallyEq_of_isCompact).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_automorphicField_realize_laws.lean

import Definitions.Def_ModularCurve_AutomorphicField
import Mathlib.Analysis.Meromorphic.Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups Topology Manifold
open UpperHalfPlane

theorem ModularCurve.automorphicField_realize_laws
    (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne] :

    (∀ (a s : ↥ModularCurve.holRing), s ≠ 0 → ∀ τ : ℍ, ∀ᶠ z in 𝓝[≠] τ,
      ModularCurve.merRealize
          (algebraMap (↥ModularCurve.holRing) (FractionRing ↥ModularCurve.holRing) a /
            algebraMap (↥ModularCurve.holRing) (FractionRing ↥ModularCurve.holRing) s) z =
        (a : ℍ → ℂ) z / (s : ℍ → ℂ) z) ∧
    (∀ (x : ↥(ModularCurve.automorphicField Γ)) (τ : ℍ),
      MeromorphicAt (fun z : ℂ => ModularCurve.automorphicField.realize x (ofComplex z)) (τ : ℂ)) ∧
    (∀ (x y : ↥(ModularCurve.automorphicField Γ)) (τ : ℍ), ∀ᶠ z in 𝓝[≠] τ,
      ModularCurve.automorphicField.realize (x + y) z =
        ModularCurve.automorphicField.realize x z + ModularCurve.automorphicField.realize y z) ∧
    (∀ (x y : ↥(ModularCurve.automorphicField Γ)) (τ : ℍ), ∀ᶠ z in 𝓝[≠] τ,
      ModularCurve.automorphicField.realize (x * y) z =
        ModularCurve.automorphicField.realize x z * ModularCurve.automorphicField.realize y z) ∧
    (∀ (c : ℂ) (τ : ℍ), ∀ᶠ z in 𝓝[≠] τ,
      ModularCurve.automorphicField.realize (algebraMap ℂ ↥(ModularCurve.automorphicField Γ) c) z = c) ∧
    (∀ x y : ↥(ModularCurve.automorphicField Γ),
      (∀ τ : ℍ, ∀ᶠ z in 𝓝[≠] τ,
        ModularCurve.automorphicField.realize x z = ModularCurve.automorphicField.realize y z) → x = y) ∧
    (∀ (x : ↥(ModularCurve.automorphicField Γ)), ∀ γ ∈ Γ, ∀ τ : ℍ, ∀ᶠ z in 𝓝[≠] τ,
      ModularCurve.automorphicField.realize x (γ • z) = ModularCurve.automorphicField.realize x z) := by sorry
