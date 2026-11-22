-- Prove2me | Theorems.Thm_LocallyConvexDuality_mackey_arens
-- name    : LocallyConvexDuality.mackey_arens
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:22:27.584591+00:00
-- url     : https://prove2.me/theorems/6973ac43-0018-4448-8c63-86cd8c95854a
-- title:
--   Mackey–Arens theorem: the locally convex topologies compatible with a dual pair are exactly those between $\sigma(E,F)$ and $\tau(E,F)$
-- statement:
--   **Mackey–Arens theorem.**
--
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$ and let $\langle E,F\rangle$ be a *dual pair*: $E,F$ are $\mathbb K$-vector spaces with a bilinear pairing $\langle\cdot,\cdot\rangle:E\times F\to\mathbb K$ which is separating ($\langle x,\cdot\rangle=0\Rightarrow x=0$ and $\langle\cdot,y\rangle=0\Rightarrow y=0$). Let
--
--   * $\sigma(E,F)$ be the weak topology on $E$;
--   * $\tau(E,F)$ be the Mackey topology on $E$, i.e. the topology of uniform convergence on all convex, circled, $\sigma(F,E)$-compact subsets of $F$.
--
--   A topology $\mathfrak T$ on $E$ is called *compatible* (or *consistent*) with the pairing if the $\mathfrak T$-continuous linear functionals on $E$ are exactly the maps $\langle\cdot,y\rangle$, $y\in F$, i.e. $(E,\mathfrak T)'=F$.
--
--   **Theorem.** Let $\mathfrak T$ be a locally convex topology on $E$. Then
--   $$\mathfrak T\ \text{is compatible with }\langle E,F\rangle\quad\Longleftrightarrow\quad \sigma(E,F)\ \subseteq\ \mathfrak T\ \subseteq\ \tau(E,F),$$
--   that is, $\mathfrak T$ is finer than the weak topology and coarser than the Mackey topology. In particular $\tau(E,F)$ is the finest locally convex topology on $E$ whose dual is $F$.
--
--   The theorem describes all locally convex topologies on $E$ with the prescribed dual $F$: they form an interval with coarsest element $\sigma(E,F)$ and finest element $\tau(E,F)$. The paper recalls it in §C.2.2.2 ("such topologies are precisely those which are finer than $\sigma(E,F)$ and coarser than the Mackey topology $\tau(E,F)$").
--
--   **Formalization Note.** The pairing is `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` with `[RCLike 𝕜]` and `hB : B.Nondegenerate` (left- and right-separating). `mackeyTopology` and `IsCompatibleTopology` are the definitions from `LocallyConvexDuality_PolarTopology`; the weak topology is the instance `TopologicalSpace (WeakBilin B)` of Mathlib, read on `E`. The topology `t` is an arbitrary term of `TopologicalSpace E` and its local convexity is the hypothesis `ht : PolynormableSpace 𝕜 E` taken with respect to `t` (the topology is defined by a family of seminorms; over `ℝ` or `ℂ` this is the same as being a locally convex vector topology). In Mathlib's order `t₁ ≤ t₂` means `t₁` is finer, so "coarser than $\tau$ and finer than $\sigma$" reads `mackeyTopology B ≤ t ∧ t ≤ σ(E,F)`. The paper speaks of Hausdorff locally convex topologies; for a separating pairing both sides of the equivalence force $\mathfrak T$ to be Hausdorff, so no Hausdorff hypothesis is needed.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 674, §C.2.2.2 (unnumbered statement of the Mackey-Arens Theorem); classical reference: H. H. Schaefer, with M. P. Wolff, Topological Vector Spaces, Second Edition, Springer, Ch. IV, 3.2-3.3 (as cited by the paper)

import Mathlib
import Definitions.Def_LocallyConvexDuality_PolarTopology

set_option autoImplicit false

namespace LocallyConvexDuality

/-- **Mackey–Arens theorem.** For a separating pairing `B : E × F → 𝕜`, a locally convex topology
`t` on `E` is compatible with the pairing iff it is coarser than the Mackey topology `τ(E, F)` and
finer than the weak topology `σ(E, F)`. (In Mathlib's order on topologies, finer means `≤`.) -/
theorem mackey_arens {𝕜 E F : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (hB : B.Nondegenerate)
    (t : TopologicalSpace E) (ht : PolynormableSpace 𝕜 E (topology := t)) :
    IsCompatibleTopology B t ↔
      mackeyTopology B ≤ t ∧ t ≤ (inferInstance : TopologicalSpace (WeakBilin B)) := by sorry

end LocallyConvexDuality
