-- Prove2me | Theorems.Thm_LocallyConvexDuality_polarTopology_finite_eq_weak
-- name    : LocallyConvexDuality.polarTopology_finite_eq_weak
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:22:32.564045+00:00
-- url     : https://prove2.me/theorems/93715645-d720-4cf8-9e0d-34a02bb6d73f
-- title:
--   The polar topology of the finite subsets of $F$ is the weak topology $\sigma(E,F)$
-- statement:
--   **Uniform convergence on finite sets is the weak topology of a pairing.**
--
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, let $E,F$ be $\mathbb K$-vector spaces and let $\langle\cdot,\cdot\rangle:E\times F\to\mathbb K$ be a bilinear pairing. For a family $\mathfrak S$ of subsets of $F$, the $\mathfrak S$-topology (polar topology) on $E$ is the topology of uniform convergence on the members of $\mathfrak S$ of the functions $y\mapsto\langle x,y\rangle$, $x\in E$. The weak topology $\sigma(E,F)$ is the coarsest topology on $E$ for which every functional $\langle\cdot,y\rangle$, $y\in F$, is continuous, i.e. the topology of pointwise convergence on $F$.
--
--   The statement is that for $\mathfrak S$ the family of all finite subsets of $F$ these two topologies coincide:
--   $$\mathfrak T_{\mathfrak S}\;=\;\sigma(E,F)\qquad\text{for }\mathfrak S=\{A\subset F:\ A\ \text{finite}\}.$$
--
--   This is the basic compatibility between the general notion of a polar topology and the weak topology: $\sigma(E,F)$ is the coarsest of the polar topologies $\mathfrak T_{\mathfrak S}$ whose family $\mathfrak S$ covers $F$ (the paper records the corresponding fact for mapping spaces in Definition C.2.1.4: the $\mathfrak S$-dual for $\mathfrak S$ the finite subsets is the weak dual $E'_\sigma$). It links the new definition `polarTopology` to Mathlib's `WeakBilin`.
--
--   **Formalization Note.** The pairing is `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` with `[RCLike 𝕜]`, and `polarTopology` is the definition from `LocallyConvexDuality_PolarTopology`. The weak topology is the instance `TopologicalSpace (WeakBilin B)` of Mathlib, read as a topology on `E` through the definitional equality `WeakBilin B = E`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 671 and 673, Definition C.2.1.4 (first item) and §C.2.2.1 (definition of the weak topology of a pairing)

import Mathlib
import Definitions.Def_LocallyConvexDuality_PolarTopology

set_option autoImplicit false

namespace LocallyConvexDuality

/-- The `𝔖`-topology of a pairing for `𝔖` = all finite subsets of `F` is the weak topology
`σ(E, F)` (the topology of Mathlib's `WeakBilin B`). -/
theorem polarTopology_finite_eq_weak {𝕜 E F : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    polarTopology B {A : Set F | A.Finite} =
      (inferInstance : TopologicalSpace (WeakBilin B)) := by sorry

end LocallyConvexDuality
