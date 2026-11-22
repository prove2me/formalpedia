-- Prove2me | Theorems.Thm_LocallyConvexDuality_nhds_zero_hasBasis_polar_equicontinuous
-- name    : LocallyConvexDuality.nhds_zero_hasBasis_polar_equicontinuous
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:21:03.629166+00:00
-- url     : https://prove2.me/theorems/841a2430-3515-4e4e-931e-21e80727276f
-- title:
--   Lemma C.2.2.2 — the polars of the weak-$*$ closed, convex, circled equicontinuous subsets of $E'$ form a base of $0$-neighbourhoods of $E$
-- statement:
--   **The topology of uniform convergence on the equicontinuous subsets of $E'$ (Lemma C.2.2.2).**
--
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, let $E$ be a Hausdorff locally convex topological $\mathbb K$-vector space with continuous dual $E'$, and let $\mathcal E$ be the collection of all subsets $M\subset E'$ that are equicontinuous, convex, circled, and closed for the weak-$*$ topology $\sigma(E',E)$ (the *equicontinuous compactology* of $E'$). For $M\subset E'$ let
--   $$M^\circ=\{x\in E:\ |\langle x,\varphi\rangle|\le 1\ \text{for all }\varphi\in M\}$$
--   be its polar in $E$ with respect to the duality $\langle E,E'\rangle$. Then the family
--   $$\mathcal U:=\{M^\circ:\ M\in\mathcal E\}$$
--   is a base of neighbourhoods of $0$ for the given topology of $E$: every $M^\circ$ with $M\in\mathcal E$ is a neighbourhood of $0$, and every neighbourhood of $0$ contains some $M^\circ$ with $M\in\mathcal E$.
--
--   In other words, the given topology of a locally convex space is the topology of uniform convergence on the equicontinuous subsets of its dual. The paper uses this for the definition of the injective tensor product topology $\otimes_\varepsilon$ and as a tool in the proofs of kernel theorems.
--
--   **Formalization Note.** `[RCLike 𝕜]`; "locally convex" is `PolynormableSpace 𝕜 E`. The base is expressed with Mathlib's `Filter.HasBasis`: the index set consists of the subsets `A` of `WeakDual 𝕜 E` (the dual with the weak-$*$ topology, so that `IsClosed A` is $\sigma(E',E)$-closedness) which are equicontinuous (Mathlib's `Equicontinuous` for the family indexed by the subtype `A`; for linear functionals this is equicontinuity at $0$), and absolutely convex (`AbsConvex 𝕜 A`: balanced, and convex for the `ComplexOrder` order on `𝕜`, i.e. for real convex combinations); the corresponding basis set is the polar `{x | ∀ f ∈ A, ‖f x‖ ≤ 1}`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 675, Lemma C.2.2.2, eq. (C.2.2.6); classical reference: H. H. Schaefer, with M. P. Wolff, Topological Vector Spaces, Second Edition, Springer, Ch. IV, Corollary 3 to 1.5 (as cited by the paper)

import Mathlib

open scoped Topology ComplexOrder

set_option autoImplicit false

namespace LocallyConvexDuality

/-- The topology of a Hausdorff locally convex space `E` is the topology of uniform convergence on
the equicontinuous subsets of its dual: the polars in `E` of the weak-* closed, absolutely convex,
equicontinuous subsets of `E'` form a basis of neighbourhoods of `0`. -/
theorem nhds_zero_hasBasis_polar_equicontinuous {𝕜 E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] [T2Space E] :
    (𝓝 (0 : E)).HasBasis
      (fun A : Set (WeakDual 𝕜 E) =>
        Equicontinuous (fun f : A => ((f : WeakDual 𝕜 E) : E → 𝕜)) ∧ AbsConvex 𝕜 A ∧ IsClosed A)
      (fun A : Set (WeakDual 𝕜 E) => {x : E | ∀ f ∈ A, ‖f x‖ ≤ 1}) := by sorry

end LocallyConvexDuality
