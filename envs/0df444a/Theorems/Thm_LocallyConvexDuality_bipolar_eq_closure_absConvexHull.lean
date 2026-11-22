-- Prove2me | Theorems.Thm_LocallyConvexDuality_bipolar_eq_closure_absConvexHull
-- name    : LocallyConvexDuality.bipolar_eq_closure_absConvexHull
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:20:52.921139+00:00
-- url     : https://prove2.me/theorems/1ccaa082-aa89-49f5-9a68-ab9bbd02b16f
-- title:
--   Bipolar theorem: $A^{\circ\circ}$ is the $\sigma(E,F)$-closure of the convex circled hull of $A\cup\{0\}$
-- statement:
--   **Bipolar theorem (for absolute polars of a bilinear pairing).**
--
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, let $E,F$ be $\mathbb K$-vector spaces and let $\langle\cdot,\cdot\rangle:E\times F\to\mathbb K$ be a bilinear pairing. For $A\subset E$ and $M\subset F$ the (absolute) polars are
--   $$A^\circ=\{y\in F:\ |\langle x,y\rangle|\le 1\ \text{for all }x\in A\}\subset F,\qquad M^\circ=\{x\in E:\ |\langle x,y\rangle|\le 1\ \text{for all }y\in M\}\subset E .$$
--   Let $\sigma(E,F)$ be the weak topology on $E$ defined by the pairing. Then for every subset $A\subset E$
--   $$(A^\circ)^\circ\;=\;\overline{\Gamma\bigl(A\cup\{0\}\bigr)}^{\,\sigma(E,F)},$$
--   where $\Gamma(S)$ denotes the convex circled (absolutely convex) hull of $S$, i.e. the set of all finite sums $\sum_i\lambda_i x_i$ with $x_i\in S$ and $\sum_i|\lambda_i|\le 1$, and the closure is taken for $\sigma(E,F)$. (For $A\ne\emptyset$ the point $0$ may be omitted.)
--
--   This is the basic tool of duality theory: it is the dictionary between subsets of $E$ and of $F$ which underlies polar topologies, the Mackey–Arens theorem and the description of a locally convex topology by equicontinuous sets (Lemma C.2.2.2 of the paper), and the paper invokes it for these purposes in §C.2.2. It is not in Mathlib, which only has $A\subset A^{\circ\circ}$ and $A^{\circ\circ\circ}=A^\circ$.
--
--   **Formalization Note.** The pairing is `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜` with `[RCLike 𝕜]`; `B.polar A ⊆ F` and `B.flip.polar M ⊆ E` are Mathlib's absolute polars (`LinearMap.polar`), `absConvexHull 𝕜` is the absolutely convex hull (balanced and convex, convexity being for the `ComplexOrder` order on `𝕜`, i.e. real convex combinations), and the closure is taken in Mathlib's weak space `WeakBilin B` (a type synonym of `E` carrying $\sigma(E,F)$). The paper states the theorem for a *duality*, i.e. a separating pairing between Hausdorff locally convex spaces; the given topologies of $E$ and $F$ do not enter the statement, and the identity holds verbatim for an arbitrary bilinear pairing, so no separation hypothesis is imposed (for a non-separating pairing $\sigma(E,F)$ is not Hausdorff; e.g. for $A=\emptyset$ both sides are the left kernel $\{x:\langle x,\cdot\rangle=0\}$ of the pairing). The paper deduces the absolute-polar form from the real-polar form of the cited reference.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 673-674, Theorem C.2.2.1 (Bi-polar Theorem), eq. (C.2.2.5); classical reference: H. H. Schaefer, with M. P. Wolff, Topological Vector Spaces, Second Edition, Springer, Ch. IV, 1.5 (the real-polar form, from which the paper deduces the stated form)

import Mathlib

open scoped ComplexOrder

set_option autoImplicit false

namespace LocallyConvexDuality

/-- **Bipolar theorem** for the absolute polars of a bilinear pairing: the bipolar of `A ⊆ E` is the
`σ(E, F)`-closure of the absolutely convex hull of `A ∪ {0}`. -/
theorem bipolar_eq_closure_absConvexHull {𝕜 E F : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) (A : Set E) :
    B.flip.polar (B.polar A) =
      closure (X := WeakBilin B) (absConvexHull 𝕜 (insert (0 : E) A)) := by sorry

end LocallyConvexDuality
