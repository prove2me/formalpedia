-- Prove2me | Theorems.Thm_OAI_BoundedHochschild_primitive_of_separable_normal_finite_paths
-- name    : OAI.BoundedHochschild.primitive_of_separable_normal_finite_paths
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:41:09.771529+00:00
-- url     : https://prove2.me/theorems/07291d6e-0eab-436a-af95-ffb2762c3551
-- title:
--   A primitive for last-slot normal cocycles under finite path tests
-- statement:
--   Throughout, $M$ is a unital C*-algebra with a partial order making it star-ordered, $X$ is a complex normed space (completeness is not assumed), and $e:X^*\to M$ is an isometric conjugate-linear isomorphism (the Lean hypothesis `e`). A family $(a_i)$ converges in the predual sense to $b$ (`PredualTendsto`) when $e^{-1}(a_i)(z)\to e^{-1}(b)(z)$ for every $z\in X$. Let $X$ be separable, and let $\tau$ be a faithful tracial positive functional in the predual with $\tau(1)=1$, with left and right multiplications having preadjoints. Assume the finite path tests (`FinitePathTests τ`): for finite data consisting of fixed unitaries indexed by $C$, words in unitaries indexed by $C\sqcup D$ in which each row $i$ contains a letter $a_i\in D$ that occurs at exactly one position of the whole array, and nontrivial reduced words $q$, for each $\varepsilon>0$ one can choose unitaries for $D$ making all traces $|\tau(q(\text{paths}))|<\varepsilon$. Let $f$ be a bounded cocycle of degree $n+1$ whose last slot is normal: $x\mapsto f(a,x)$ has a preadjoint for each $a$. Then there is $g$ with $\|g\|\le\|f\|$ and $\partial g=f$. Here a cochain of degree $k$ is a bounded complex $k$-linear map $M^k\to M$, and $\partial$ (`differentialValue`) is the Hochschild differential $(\partial f)(v_0,\dots,v_k)=v_0f(v_1,\dots,v_k)+\sum_{j<k}(-1)^{j+1}f(\dots,v_jv_{j+1},\dots)+(-1)^{k+1}f(v_0,\dots,v_{k-1})v_k$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.BoundedHochschild.primitive_of_separable_normal_finite_paths`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/BoundedHochschild/SeparablePrimitives.lean#L109

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
open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ)

end BoundedHochschild

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildWalk HochschildRare
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [TopologicalSpace.SeparableSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

theorem primitive_of_separable_normal_finite_paths
    (h1 : τ 1=1) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hR : ∀ b : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip b))
    (hτ : TraceInPredual e τ) (hpaths : FinitePathTests τ)
    {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ x : Fin (n+2) → M, differentialValue f x=0)
    (hnormal : ∀ a : Fin n → M, HasPreadjoint e (f.curryRight a)) :
    ∃ g : Cochain M n, ‖g‖ ≤ ‖f‖ ∧ ∀ x, differentialValue g x=f x := by
  sorry

end BoundedHochschild
end
end OAI
