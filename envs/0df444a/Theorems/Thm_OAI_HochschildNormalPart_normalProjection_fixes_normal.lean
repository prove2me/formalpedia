-- Prove2me | Theorems.Thm_OAI_HochschildNormalPart_normalProjection_fixes_normal
-- name    : OAI.HochschildNormalPart.normalProjection_fixes_normal
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:40:49.827024+00:00
-- url     : https://prove2.me/theorems/2739dce3-5fca-418d-ac1a-5cddc251a775
-- title:
--   The normal projection preserves normal coefficients
-- statement:
--   Let $M$ be a unital C*-algebra with predual $X$ through an isometric conjugate-linear isomorphism $e:X^*\to M$, and $\pi:M\to B(H)$ a unital *-homomorphism on a Hilbert space. For $\eta,\xi\in H$ let $\omega_{\eta,\xi}(a)=\langle\eta,\pi(a)\xi\rangle$ (`coefficient π η ξ`). Let $P$ be the orthogonal projection (`normalProjection e π`) onto the closed subspace of vectors $\xi$ for which $\omega_{\zeta,\xi}$ is normal for all $\zeta$ (`normalVectors e π`). If $\omega_{\eta,\xi}$ is normal, then
--
--   $$\omega_{\eta,P\xi}=\omega_{\eta,\xi}.$$
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.HochschildNormalPart.normalProjection_fixes_normal`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/BoundedHochschild/NormalVectors.lean#L269

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
namespace HochschildNormalPart
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

variable [CompleteSpace X]

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (π : M →⋆ₐ[ℂ] (H →L[ℂ] H))

theorem normalProjection_fixes_normal (η ξ : H)
    (h : coefficient π η ξ ∈ normalDual e) :
    coefficient π η (normalProjection e π ξ)=coefficient π η ξ := by
  sorry

end HochschildNormalPart
end
end OAI
