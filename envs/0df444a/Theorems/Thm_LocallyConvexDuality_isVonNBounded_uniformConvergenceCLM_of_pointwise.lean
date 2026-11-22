-- Prove2me | Theorems.Thm_LocallyConvexDuality_isVonNBounded_uniformConvergenceCLM_of_pointwise
-- name    : LocallyConvexDuality.isVonNBounded_uniformConvergenceCLM_of_pointwise
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:20:56.067801+00:00
-- url     : https://prove2.me/theorems/d74d2eff-071a-4f66-9e97-abb1b2ec8fc8
-- title:
--   Pointwise bounded sets of operators on a quasi-complete locally convex space are bounded for every $\mathfrak S$-topology
-- statement:
--   **Pointwise bounded sets of operators on a quasi-complete space are bounded for every $\mathfrak S$-topology.**
--
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, and let $E,F$ be Hausdorff locally convex topological $\mathbb K$-vector spaces with $E$ quasi-complete (every closed bounded subset of $E$ is complete). Let $H\subset\mathscr L(E,F)$ be a set of continuous linear maps which is bounded for the topology of pointwise convergence, that is,
--   $$\{f(x):\ f\in H\}\ \text{is bounded in }F\qquad\text{for every }x\in E .$$
--   Then $H$ is bounded in $\mathscr L_{\mathfrak S}(E,F)$ for every family $\mathfrak S$ of bounded subsets of $E$; equivalently, for every $T\in\mathfrak S$ the set
--   $$H(T)=\{f(x):\ f\in H,\ x\in T\}$$
--   is bounded in $F$. In particular (taking for $\mathfrak S$ all bounded subsets of $E$) $H$ is bounded for the topology of bounded convergence $\mathscr L_\beta(E,F)$.
--
--   Note that $E$ is not assumed to be barrelled: this is a boundedness principle of Banach–Mackey type, weaker than equicontinuity. The paper records it in §C.2.1 as "an important property of $\mathfrak S$-topologies" (for $\mathfrak S$ a directed family of bounded sets covering $E$); it shows that on a quasi-complete space all $\mathfrak S$-topologies with $\mathfrak S$ covering $E$ have the same bounded sets.
--
--   **Formalization Note.** `[RCLike 𝕜]`; "locally convex" is `PolynormableSpace 𝕜` (topology defined by seminorms), the uniform structures of `E` and `F` are the ones of the topological additive groups (`IsUniformAddGroup`), quasi-completeness is Mathlib's `QuasiCompleteSpace 𝕜 E`, and boundedness is von Neumann boundedness. The conclusion is boundedness of the image of `H` in Mathlib's `E →Lᵤ[𝕜, 𝔖] F` (`UniformConvergenceCLM`), into which `H` is transported by the identity map `UniformConvergenceCLM.ofFun`. The hypothesis `hH` is pointwise boundedness, which is the same as boundedness for the topology of pointwise convergence. The family `𝔖` is an arbitrary family of bounded sets: the paper's requirements that `𝔖` be directed and cover `E` are not needed for this implication and are not imposed.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 672, §C.2.1 (unnumbered paragraph before Lemma C.2.1.7); classical reference: H. H. Schaefer, with M. P. Wolff, Topological Vector Spaces, Second Edition, Springer, Ch. III, Corollary to 3.4 (as cited by the paper)

import Mathlib

open scoped UniformConvergenceCLM

set_option autoImplicit false

namespace LocallyConvexDuality

/-- If `E` is a quasi-complete Hausdorff locally convex space and `F` a Hausdorff locally convex
space, then every pointwise bounded set `H` of continuous linear maps `E → F` is bounded for the
topology of uniform convergence on the members of any family `𝔖` of bounded subsets of `E`. -/
theorem isVonNBounded_uniformConvergenceCLM_of_pointwise {𝕜 E F : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
    [PolynormableSpace 𝕜 E] [T2Space E] [QuasiCompleteSpace 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] [UniformSpace F] [IsUniformAddGroup F] [ContinuousSMul 𝕜 F]
    [PolynormableSpace 𝕜 F] [T2Space F]
    (𝔖 : Set (Set E)) (h𝔖 : ∀ S ∈ 𝔖, Bornology.IsVonNBounded 𝕜 S)
    (H : Set (E →L[𝕜] F))
    (hH : ∀ x : E, Bornology.IsVonNBounded 𝕜 ((fun f : E →L[𝕜] F => f x) '' H)) :
    Bornology.IsVonNBounded 𝕜 (UniformConvergenceCLM.ofFun (RingHom.id 𝕜) F 𝔖 '' H) := by sorry

end LocallyConvexDuality
