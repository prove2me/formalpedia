-- Prove2me | Theorems.Thm_LocallyConvexDuality_uniformConvergenceCLM_withSeminorms
-- name    : LocallyConvexDuality.uniformConvergenceCLM_withSeminorms
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:20:55.215091+00:00
-- url     : https://prove2.me/theorems/dcc49aa1-a773-43e3-b91d-0ded66b1c43a
-- title:
--   The seminorms $q_{T,i}(f)=\sup_{x\in T}\nu_i(f(x))$ generate the $\mathfrak S$-topology of $\mathscr L(E,F)$
-- statement:
--   **Seminorms defining the topology of uniform convergence on a family of bounded sets.**
--
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, let $E$ and $F$ be Hausdorff topological $\mathbb K$-vector spaces with $F$ locally convex, and let $\{\nu_i\}_{i\in I}$ be a family of seminorms generating the topology of $F$. Let $\mathfrak S$ be a family of bounded subsets of $E$, and let $\mathscr L_{\mathfrak S}(E,F)$ be the space $\mathscr L(E,F)$ of continuous linear maps $E\to F$ with the $\mathfrak S$-topology, i.e. the topology of uniform convergence on the members of $\mathfrak S$. For $(T,i)\in\mathfrak S\times I$ put
--   $$q_{T,i}(f)\;:=\;\sup_{x\in T}\,\nu_i\bigl(f(x)\bigr),\qquad f\in\mathscr L(E,F).$$
--   Then each $q_{T,i}$ is a (finite) seminorm on $\mathscr L(E,F)$, and the family $\{q_{T,i}\}_{(T,i)\in\mathfrak S\times I}$ generates the $\mathfrak S$-topology of $\mathscr L_{\mathfrak S}(E,F)$.
--
--   This makes the local convexity of $\mathscr L_{\mathfrak S}(E,F)$ explicit (paper, eq. (C.2.1.4)) and contains as special cases the seminorms $f\mapsto\nu_i(f(u))$ of the topology of pointwise convergence, the seminorms of the strong dual $E'_\beta$, and the operator norm for normed spaces. Mathlib has a statement of this kind only for the topology of pointwise convergence with values in a normed space.
--
--   **Formalization Note.** The space $\mathscr L_{\mathfrak S}(E,F)$ is Mathlib's `E →Lᵤ[𝕜, 𝔖] F` (`UniformConvergenceCLM`), with `[RCLike 𝕜]`; "generates the topology" is Mathlib's `WithSeminorms`, both for the given family `p` on `F` (hypothesis `hp`, which also encodes that `F` is locally convex) and for the family `q` on `E →Lᵤ[𝕜, 𝔖] F`. Since the supremum of a real-valued function is only meaningful when it is bounded, the statement is packaged as the existence of a seminorm family `q` indexed by `𝔖 × ι` whose values are the suprema `⨆ x : T, p i (f x)` (these are bounded above because `f '' T` is bounded) and which generates the topology; the values determine `q` uniquely. The family `𝔖` is an arbitrary family of von Neumann bounded sets: it need not be directed, and the paper's standing requirement that the union of `𝔖` span a dense subspace (which only serves to make $\mathscr L_{\mathfrak S}(E,F)$ Hausdorff) is not needed for the statement and is not imposed.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 671, eq. (C.2.1.4) with (C.2.1.3) (unnumbered statement after Lemma C.2.1.2); classical reference: H. H. Schaefer, with M. P. Wolff, Topological Vector Spaces, Second Edition, Springer, Ch. III, p. 81 (as cited by the paper)

import Mathlib

open scoped UniformConvergenceCLM

set_option autoImplicit false

namespace LocallyConvexDuality

/-- If the seminorms `p i` generate the topology of `F` and `𝔖` is a family of bounded subsets of
`E`, then the seminorms `q (T, i) f = ⨆ x ∈ T, p i (f x)`, `(T, i) ∈ 𝔖 × ι`, generate the topology
of uniform convergence on the members of `𝔖` on the space of continuous linear maps `E → F`. -/
theorem uniformConvergenceCLM_withSeminorms {𝕜 E F ι : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [T2Space E]
    [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul 𝕜 F] [T2Space F]
    (p : SeminormFamily 𝕜 F ι) (hp : WithSeminorms p)
    (𝔖 : Set (Set E)) (h𝔖 : ∀ S ∈ 𝔖, Bornology.IsVonNBounded 𝕜 S) :
    ∃ q : SeminormFamily 𝕜 (E →Lᵤ[𝕜, 𝔖] F) (𝔖 × ι),
      (∀ (T : 𝔖) (i : ι) (f : E →Lᵤ[𝕜, 𝔖] F), q (T, i) f = ⨆ x : (T : Set E), p i (f x)) ∧
        WithSeminorms q := by sorry

end LocallyConvexDuality
