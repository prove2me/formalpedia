-- Prove2me | Theorems.Thm_OAI_HochschildNormalPart_normalProjection_sum
-- name    : OAI.HochschildNormalPart.normalProjection_sum
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:41:46.101068+00:00
-- url     : https://prove2.me/theorems/1e84faad-075a-4832-906d-60ac32e1a828
-- title:
--   The normal projection of a direct sum representation
-- statement:
--   Let $M$ be a unital C*-algebra with predual $X$ through $e:X^*\cong M$, and let $\pi:M\to B(H)$, $\rho:M\to B(K)$ be unital *-homomorphisms on Hilbert spaces. The normal projection (`normalProjection`, the orthogonal projection onto vectors all of whose coefficients are normal) of the direct sum representation on $H\oplus_2K$ (`sumRepresentation π ρ`) acts componentwise:
--
--   $$P_{\pi\oplus\rho}(\xi_1,\xi_2)=(P_\pi\xi_1,P_\rho\xi_2).$$
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.HochschildNormalPart.normalProjection_sum`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/BoundedHochschild/NormalVectors.lean#L378

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

end HochschildNormalPart

open scoped InnerProductSpace
namespace HochschildNormalPart
universe u v w
variable {M : Type u} [CStarAlgebra M]
variable {H : Type v} {K : Type w}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
  (π : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : M →⋆ₐ[ℂ] (K →L[ℂ] K))

theorem normalProjection_sum (ξ : WithLp 2 (H×K)) :
    normalProjection e (sumRepresentation π ρ) ξ=
      WithLp.toLp 2 (normalProjection e π ξ.fst,normalProjection e ρ ξ.snd) := by
  sorry

end HochschildNormalPart
end
end OAI
