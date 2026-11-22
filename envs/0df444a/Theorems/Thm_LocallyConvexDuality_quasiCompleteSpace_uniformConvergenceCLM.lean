-- Prove2me | Theorems.Thm_LocallyConvexDuality_quasiCompleteSpace_uniformConvergenceCLM
-- name    : LocallyConvexDuality.quasiCompleteSpace_uniformConvergenceCLM
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:20:58.086647+00:00
-- url     : https://prove2.me/theorems/1441aab5-3a92-4e08-a373-3c744f791d9e
-- title:
--   Lemma C.2.1.7 — $\mathscr L_{\mathfrak S}(E,F)$ is quasi-complete for $E$ barrelled and $F$ quasi-complete
-- statement:
--   **Quasi-completeness of mapping spaces (Lemma C.2.1.7).**
--
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$ and let $E,F$ be Hausdorff locally convex topological $\mathbb K$-vector spaces. Assume
--
--   1. $E$ is barrelled;
--   2. $F$ is quasi-complete, i.e. every closed bounded subset of $F$ is complete;
--   3. $\mathfrak S$ is a family of bounded subsets of $E$ whose union is $E$.
--
--   Let $\mathscr L_{\mathfrak S}(E,F)$ be the space of continuous linear maps $E\to F$ with the $\mathfrak S$-topology (uniform convergence on the members of $\mathfrak S$). Then
--   $$\mathscr L_{\mathfrak S}(E,F)\ \text{is quasi-complete.}$$
--
--   In particular, for $E$ barrelled and $F$ quasi-complete, $\mathscr L_\sigma(E,F)$ (pointwise convergence) and $\mathscr L_\beta(E,F)$ (bounded convergence) are quasi-complete, and so are the weak dual $E'_\sigma$ and the strong dual $E'_\beta$ of a barrelled space. The paper applies the lemma in Remark C.2.1.8 to the algebra of bounded operators on a Hilbert space with the strong operator topology.
--
--   **Formalization Note.** `[RCLike 𝕜]`; "locally convex" is `PolynormableSpace 𝕜`, the uniform structures are those of the topological additive groups (`IsUniformAddGroup`), "barrelled" is Mathlib's `BarrelledSpace 𝕜 E` (every lower semicontinuous seminorm is continuous, which for a locally convex space is equivalent to: every barrel is a neighbourhood of $0$), and quasi-completeness is Mathlib's `QuasiCompleteSpace 𝕜` (closed von Neumann bounded sets are complete). The mapping space is Mathlib's `E →Lᵤ[𝕜, 𝔖] F` (`UniformConvergenceCLM`) with its uniform structure of uniform convergence on the members of `𝔖`. The paper asks `𝔖` to be directed under inclusion ("cofiltered"); Mathlib's uniform structure is defined for an arbitrary family and is unchanged when `𝔖` is replaced by the family of finite unions of its members, so directedness is not imposed.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 672, Lemma C.2.1.7; classical reference: H. H. Schaefer, with M. P. Wolff, Topological Vector Spaces, Second Edition, Springer, Ch. III, Corollary to 4.4 (as cited by the paper)

import Mathlib

open scoped UniformConvergenceCLM

set_option autoImplicit false

namespace LocallyConvexDuality

/-- If `E` is a barrelled Hausdorff locally convex space, `F` a quasi-complete Hausdorff locally
convex space and `𝔖` a family of bounded subsets of `E` covering `E`, then the space of continuous
linear maps `E → F` with the topology of uniform convergence on the members of `𝔖` is
quasi-complete. -/
theorem quasiCompleteSpace_uniformConvergenceCLM {𝕜 E F : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
    [PolynormableSpace 𝕜 E] [T2Space E] [BarrelledSpace 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] [UniformSpace F] [IsUniformAddGroup F] [ContinuousSMul 𝕜 F]
    [PolynormableSpace 𝕜 F] [T2Space F] [QuasiCompleteSpace 𝕜 F]
    (𝔖 : Set (Set E)) (h𝔖 : ∀ S ∈ 𝔖, Bornology.IsVonNBounded 𝕜 S) (hcov : ⋃₀ 𝔖 = Set.univ) :
    QuasiCompleteSpace 𝕜 (E →Lᵤ[𝕜, 𝔖] F) := by sorry

end LocallyConvexDuality
