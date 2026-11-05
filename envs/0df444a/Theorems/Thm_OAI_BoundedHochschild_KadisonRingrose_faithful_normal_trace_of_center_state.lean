-- Prove2me | Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_faithful_normal_trace_of_center_state
-- name    : OAI.BoundedHochschild.KadisonRingrose.faithful_normal_trace_of_center_state
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:41:58.952064+00:00
-- url     : https://prove2.me/theorems/d7eca542-fedf-4ae8-9526-be45d92b2f95
-- title:
--   A faithful normal tracial state from a state faithful on central projections
-- statement:
--   Throughout, $M$ is a unital C*-algebra with a partial order making it star-ordered, $X$ is a complex Banach space, and $e:X^*\to M$ is an isometric conjugate-linear isomorphism, so $M$ is a von Neumann algebra with predual $X$ (the Lean hypothesis `e`). Let $M$ be finite (`FiniteAlgebra M`) and $\psi$ a positive functional in the predual (`TraceInPredual e ψ`) with $\psi(1)=1$ that does not vanish on nonzero central projections. Then there is a positive functional $\tau$ in the predual with $\tau(1)=1$, $\tau(ab)=\tau(ba)$, and $\tau(a^*a)=0\Rightarrow a=0$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.BoundedHochschild.KadisonRingrose.faithful_normal_trace_of_center_state`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/BoundedHochschild/FiniteTracialDecomposition.lean#L29

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

namespace OAI

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildCorners

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem faithful_normal_trace_of_center_state (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ)
    (hψ1 : ψ 1 = 1)
    (hfaith : ∀ p : M, IsStarProjection p → (∀ a : M, p * a = a * p) → ψ p = 0 → p = 0) :
    ∃ τ : M →ₚ[ℂ] ℂ, TraceInPredual e τ ∧ τ 1 = 1 ∧
      (∀ a b : M, τ (a * b) = τ (b * a)) ∧
      ∀ a : M, τ (star a * a) = 0 → a = 0 := by
  sorry

end KadisonRingrose
end BoundedHochschild
end
end OAI
