-- Prove2me | Theorems.Thm_LocallyConvexDuality_isVonNBounded_uniformConvergenceCLM_of_equicontinuous
-- name    : LocallyConvexDuality.isVonNBounded_uniformConvergenceCLM_of_equicontinuous
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:20:59.957568+00:00
-- url     : https://prove2.me/theorems/51afc994-65c3-4939-baf7-dbc24c7bacc4
-- title:
--   Lemma C.2.1.9(1) — equicontinuous sets of operators are bounded in $\mathscr L_{\mathfrak S}(E,F)$
-- statement:
--   **Equicontinuous sets of operators are bounded for every $\mathfrak S$-topology (Lemma C.2.1.9(1)).**
--
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, let $E,F$ be Hausdorff locally convex topological $\mathbb K$-vector spaces, and let $H\subset\mathscr L(E,F)$ be an *equicontinuous* set of continuous linear maps: for every $0$-neighbourhood $V\subset F$ there is a $0$-neighbourhood $U\subset E$ with $f(U)\subset V$ for all $f\in H$. Let $\mathfrak S$ be a family of bounded subsets of $E$. Then $H$ is bounded in $\mathscr L_{\mathfrak S}(E,F)$, the space $\mathscr L(E,F)$ with the topology of uniform convergence on the members of $\mathfrak S$; equivalently, for every $T\in\mathfrak S$ the set
--   $$H(T)=\{f(x):\ f\in H,\ x\in T\}$$
--   is bounded in $F$.
--
--   Together with the Banach–Steinhaus theorem (on a barrelled space every pointwise bounded set of operators is equicontinuous) this is how boundedness in the strong topologies of $\mathscr L(E,F)$ and of duals is usually obtained. The paper lists it among the "important properties of equicontinuous subsets" in §C.2.1.
--
--   **Formalization Note.** `[RCLike 𝕜]`; "locally convex" is `PolynormableSpace 𝕜` and the uniform structures are those of the topological additive groups. Equicontinuity is Mathlib's `Equicontinuous` for the family `H → (E → F)` indexed by the subtype `H`; for linear maps this is equivalent to equicontinuity at $0$, which is the definition recalled in the paper. The conclusion is von Neumann boundedness of the image of `H` in Mathlib's `E →Lᵤ[𝕜, 𝔖] F` (`UniformConvergenceCLM`) under the identity map `UniformConvergenceCLM.ofFun`. The paper also asks that the union of `𝔖` span a dense subspace of `E` (its standing condition making $\mathscr L_{\mathfrak S}(E,F)$ Hausdorff); this plays no role for boundedness and is not imposed.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 672, Lemma C.2.1.9(1); classical reference: H. H. Schaefer, with M. P. Wolff, Topological Vector Spaces, Second Edition, Springer, Ch. III, Corollary to 4.1 and 4.5 (as cited by the paper for Lemma C.2.1.9)

import Mathlib

open scoped UniformConvergenceCLM

set_option autoImplicit false

namespace LocallyConvexDuality

/-- An equicontinuous set `H` of continuous linear maps `E → F` is bounded for the topology of
uniform convergence on the members of any family `𝔖` of bounded subsets of `E`. -/
theorem isVonNBounded_uniformConvergenceCLM_of_equicontinuous {𝕜 E F : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
    [PolynormableSpace 𝕜 E] [T2Space E]
    [AddCommGroup F] [Module 𝕜 F] [UniformSpace F] [IsUniformAddGroup F] [ContinuousSMul 𝕜 F]
    [PolynormableSpace 𝕜 F] [T2Space F]
    (𝔖 : Set (Set E)) (h𝔖 : ∀ S ∈ 𝔖, Bornology.IsVonNBounded 𝕜 S)
    (H : Set (E →L[𝕜] F))
    (hH : Equicontinuous (fun f : H => ((f : E →L[𝕜] F) : E → F))) :
    Bornology.IsVonNBounded 𝕜 (UniformConvergenceCLM.ofFun (RingHom.id 𝕜) F 𝔖 '' H) := by sorry

end LocallyConvexDuality
