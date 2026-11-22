-- Prove2me | Theorems.Thm_LocallyConvexDuality_induced_pointwise_eq_induced_precompact_of_equicontinuous
-- name    : LocallyConvexDuality.induced_pointwise_eq_induced_precompact_of_equicontinuous
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:20:58.367983+00:00
-- url     : https://prove2.me/theorems/29bded7e-f6b6-46a4-be03-1d4d26816bda
-- title:
--   Lemma C.2.1.9(2) — on an equicontinuous set of operators, pointwise and precompact convergence induce the same topology
-- statement:
--   **On equicontinuous sets, pointwise convergence equals precompact convergence (Lemma C.2.1.9(2)).**
--
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, let $E,F$ be Hausdorff locally convex topological $\mathbb K$-vector spaces, and let $H\subset\mathscr L(E,F)$ be an equicontinuous set of continuous linear maps (for every $0$-neighbourhood $V\subset F$ there is a $0$-neighbourhood $U\subset E$ with $f(U)\subset V$ for all $f\in H$). Consider on $\mathscr L(E,F)$
--
--   * the topology of simple (pointwise) convergence, $\mathscr L_\sigma(E,F)$: uniform convergence on the finite subsets of $E$;
--   * the topology of precompact convergence, $\mathscr L_\gamma(E,F)$: uniform convergence on the precompact (totally bounded) subsets of $E$.
--
--   Then the two topologies induce the same topology on $H$:
--   $$\mathscr L_\sigma(E,F)\big|_H\;=\;\mathscr L_\gamma(E,F)\big|_H .$$
--   Concretely, a net $(f_\alpha)$ in $H$ which converges pointwise to some $f\in H$ converges to $f$ uniformly on every precompact subset of $E$.
--
--   This is the Ascoli-type statement behind compactness arguments in duals and operator spaces (e.g. on an equicontinuous subset of $E'$ the weak-$*$ topology coincides with the topology of precompact convergence); the paper notes that precompact convergence is the topology relevant for traces of nuclear operators. Mathlib has the analogous statement for uniform convergence on *compact* sets and general equicontinuous families, but not the precompact version, which uses linearity.
--
--   **Formalization Note.** `[RCLike 𝕜]`; "locally convex" is `PolynormableSpace 𝕜`, and the uniform structures of `E` and `F` are those of the topological additive groups (`IsUniformAddGroup`), so that `TotallyBounded` is precompactness in the sense of the paper (relatively compact in the completion). Both topologies on the subtype `H` are written as `TopologicalSpace.induced` along the inclusion of `H` into Mathlib's `E →Lᵤ[𝕜, 𝔖] F` (`UniformConvergenceCLM`), for `𝔖 = {S | S.Finite}` and `𝔖 = {S | TotallyBounded S}` respectively; the first space is Mathlib's space of pointwise convergence `E →Lₚₜ[𝕜] F`. Equicontinuity is Mathlib's `Equicontinuous` for the family indexed by the subtype `H` (equivalent, for linear maps, to equicontinuity at $0$).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 672, Lemma C.2.1.9(2); classical reference: H. H. Schaefer, with M. P. Wolff, Topological Vector Spaces, Second Edition, Springer, Ch. III, Corollary to 4.1 and 4.5 (as cited by the paper for Lemma C.2.1.9)

import Mathlib

open scoped UniformConvergenceCLM

set_option autoImplicit false

namespace LocallyConvexDuality

/-- On an equicontinuous set `H` of continuous linear maps `E → F`, the topology of pointwise
convergence and the topology of uniform convergence on totally bounded (precompact) subsets of `E`
induce the same topology. -/
theorem induced_pointwise_eq_induced_precompact_of_equicontinuous {𝕜 E F : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
    [PolynormableSpace 𝕜 E] [T2Space E]
    [AddCommGroup F] [Module 𝕜 F] [UniformSpace F] [IsUniformAddGroup F] [ContinuousSMul 𝕜 F]
    [PolynormableSpace 𝕜 F] [T2Space F]
    (H : Set (E →L[𝕜] F))
    (hH : Equicontinuous (fun f : H => ((f : E →L[𝕜] F) : E → F))) :
    TopologicalSpace.induced
        (fun f : H => UniformConvergenceCLM.ofFun (RingHom.id 𝕜) F {S : Set E | S.Finite}
          (f : E →L[𝕜] F))
        inferInstance =
      TopologicalSpace.induced
        (fun f : H => UniformConvergenceCLM.ofFun (RingHom.id 𝕜) F {S : Set E | TotallyBounded S}
          (f : E →L[𝕜] F))
        inferInstance := by sorry

end LocallyConvexDuality
