-- Prove2me | Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_normal_positive_predual_orbit_compact
-- name    : OAI.BoundedHochschild.KadisonRingrose.normal_positive_predual_orbit_compact
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:41:40.310011+00:00
-- url     : https://prove2.me/theorems/532144fa-71a8-4d93-94b1-8a99084078f5
-- title:
--   Weak compactness of the predual orbit of a normal positive functional
-- statement:
--   Throughout, $M$ is a unital C*-algebra with a partial order making it star-ordered, $X$ is a complex Banach space, and $e:X^*\to M$ is an isometric conjugate-linear isomorphism, so $M$ is a von Neumann algebra with predual $X$ (the Lean hypothesis `e`). Let $M$ be finite and $\psi$ a positive functional in the predual. Let $\mathcal K$ be the weak-* closure in $M^*$ of the unitary orbit hull of $\psi$ (`weakFunctionalClosure (unitaryOrbitHull ...)`). Then the preimage of $\mathcal K$ under the canonical map from $X$ with its weak topology to the weak-* dual of $M$ (`weakPredualMap e`) is compact.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.BoundedHochschild.KadisonRingrose.normal_positive_predual_orbit_compact`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/BoundedHochschild/WeakPredual.lean#L71

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

namespace OAI

noncomputable section

open Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

variable [PartialOrder M] [StarOrderedRing M] [CompleteSpace X]

theorem normal_positive_predual_orbit_compact (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ) :
    IsCompact ((weakPredualMap e) ⁻¹'
      weakFunctionalClosure (unitaryOrbitHull (positiveFunctionalCLM ψ))) := by
  sorry

end KadisonRingrose
end BoundedHochschild
end
end OAI
