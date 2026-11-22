-- Prove2me | Theorems.Thm_LocallyConvexDuality_barrelledSpace_iff_eq_strongTopology
-- name    : LocallyConvexDuality.barrelledSpace_iff_eq_strongTopology
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:22:30.897339+00:00
-- url     : https://prove2.me/theorems/ef9636bf-42a0-4256-8de7-3986ea222b8c
-- title:
--   A locally convex space $E$ is barrelled iff its topology is the strong topology $\beta(E,E')$
-- statement:
--   **A locally convex space is barrelled iff it carries the strong topology $\beta(E,E')$.**
--
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, let $E$ be a locally convex topological $\mathbb K$-vector space with topology $\mathfrak T$, let $E'$ be its continuous dual, and consider the canonical pairing $\langle x,f\rangle=f(x)$ between $E$ and $E'$. The strong topology $\beta(E,E')$ on $E$ is the topology of uniform convergence on the $\sigma(E',E)$-bounded subsets of $E'$; a base of $0$-neighbourhoods is given by the polars
--   $$H^\circ=\{x\in E:\ |f(x)|\le 1\ \text{for all }f\in H\},\qquad H\subset E'\ \ \sigma(E',E)\text{-bounded},$$
--   which are exactly the barrels of $E$. Then
--   $$E\ \text{is barrelled}\quad\Longleftrightarrow\quad \mathfrak T=\beta(E,E').$$
--
--   For every locally convex space $\beta(E,E')$ is finer than $\mathfrak T$, and it is the finest of the topologies of uniform convergence on families of $\sigma(E',E)$-bounded subsets of $E'$; the theorem says that the barrelled spaces are exactly the locally convex spaces for which this finest topology is the given one.
--
--   **Deviation from the source.** The paper writes at this place that "the condition under which the strong-dual topology $\beta(E',E)$ agrees with the Mackey topology $\tau(E',E)$ is barreledness of $E$". In that sentence the roles of $E$ and $E'$ are interchanged and the statement is false as written (the Banach space $c_0$ is barrelled, but $\beta(\ell^1,c_0)\neq\tau(\ell^1,c_0)$: the first has dual $\ell^\infty$, the second $c_0$; the equality $\beta(E',E)=\tau(E',E)$ characterises semi-reflexive spaces). The correct classical statement, formalized here, concerns the strong topology on $E$ itself: barrelledness of $E$ means that $E$ carries $\beta(E,E')$.
--
--   **Formalization Note.** `[RCLike 𝕜]`; "locally convex" is `PolynormableSpace 𝕜 E` (no Hausdorff hypothesis is needed), "barrelled" is Mathlib's `BarrelledSpace 𝕜 E` (every lower semicontinuous seminorm is continuous; for locally convex spaces this is equivalent to: every barrel is a neighbourhood of $0$). The pairing is `(topDualPairing 𝕜 E).flip : E →ₗ[𝕜] (E →L[𝕜] 𝕜) →ₗ[𝕜] 𝕜`, `(x, f) ↦ f x`, and `strongTopology` is the definition from `LocallyConvexDuality_PolarTopology`: the topology on `E` of uniform convergence on the subsets of `E →L[𝕜] 𝕜` that are von Neumann bounded for the weak-$*$ topology. The given topology of `E` is the named instance `t`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 674, §C.2.2.2 (unnumbered sentence relating barrelledness and strong topologies, in corrected form: see the deviation recorded in the statement); the paper refers at this place to H. H. Schaefer, with M. P. Wolff, Topological Vector Spaces, Second Edition, Springer, Ch. IV, 5.2 and Ch. II, §7

import Mathlib
import Definitions.Def_LocallyConvexDuality_PolarTopology

set_option autoImplicit false

namespace LocallyConvexDuality

/-- A locally convex space `E` is barrelled iff its topology coincides with the strong topology
`β(E, E')` of the canonical pairing between `E` and its continuous dual `E'`, i.e. with the topology
of uniform convergence on the `σ(E', E)`-bounded subsets of `E'`. -/
theorem barrelledSpace_iff_eq_strongTopology {𝕜 E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [t : TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] :
    BarrelledSpace 𝕜 E ↔ strongTopology (topDualPairing 𝕜 E).flip = t := by sorry

end LocallyConvexDuality
