-- Prove2me | Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_normal_positive_uniform_orbit_hull
-- name    : OAI.BoundedHochschild.KadisonRingrose.normal_positive_uniform_orbit_hull
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:42:31.043755+00:00
-- url     : https://prove2.me/theorems/600f8b79-c2a7-4ac3-a6b2-746333394bbb
-- title:
--   Uniform smallness of a normal positive orbit on orthogonal projections
-- statement:
--   Throughout, $M$ is a unital C*-algebra with a partial order making it star-ordered, $X$ is a complex Banach space, and $e:X^*\to M$ is an isometric conjugate-linear isomorphism, so $M$ is a von Neumann algebra with predual $X$ (the Lean hypothesis `e`). Let $M$ be finite and $\psi$ a positive functional in the predual. Let $(q_n)$ be pairwise orthogonal projections and $\varepsilon>0$. Then, for all large $n$, every functional $G$ in the norm-closed convex hull of the unitary pullbacks of $\psi$ (`unitaryOrbitHull`, with pullback $a\mapsto\psi(uau^*)$) satisfies
--
--   $$|G(q_n)|<\varepsilon.$$
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.BoundedHochschild.KadisonRingrose.normal_positive_uniform_orbit_hull`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/BoundedHochschild/NormalOrbitHull.lean#L106

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem normal_positive_uniform_orbit_hull (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ)
    (q : ℕ → M) (hq : ∀ n, IsStarProjection (q n))
    (horth : ∀ i j, i ≠ j → q i * q j = 0) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ G ∈ unitaryOrbitHull (positiveFunctionalCLM ψ), ‖G (q n)‖ < ε := by
  sorry

end KadisonRingrose
end BoundedHochschild
end
end OAI
