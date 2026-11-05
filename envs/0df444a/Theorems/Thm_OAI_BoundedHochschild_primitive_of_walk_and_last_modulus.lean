-- Prove2me | Theorems.Thm_OAI_BoundedHochschild_primitive_of_walk_and_last_modulus
-- name    : OAI.BoundedHochschild.primitive_of_walk_and_last_modulus
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:42:29.939507+00:00
-- url     : https://prove2.me/theorems/88f0539d-f119-4d61-9219-38b2b901febb
-- title:
--   A primitive from a free walk and a last-slot modulus
-- statement:
--   Throughout, $M$ is a unital C*-algebra with a partial order making it star-ordered, $X$ is a complex normed space (completeness is not assumed), and $e:X^*\to M$ is an isometric conjugate-linear isomorphism (the Lean hypothesis `e`). A family $(a_i)$ converges in the predual sense to $b$ (`PredualTendsto`) when $e^{-1}(a_i)(z)\to e^{-1}(b)(z)$ for every $z\in X$. Let $\tau$ be a positive functional in the predual (`TraceInPredual`), faithful, tracial, $\tau(1)=1$, and assume left and right multiplications have preadjoints. Let $G$ be a countable group, $\rho:G\to U(M)$ a homomorphism, and $\mu=\sum_jp_j\delta_{a_j}$ a symmetric atomic probability measure (`atomicLaw p atoms`) with free moments in probability (`FreeMomentsInProbability`) along $t(k)\to\infty$. Assume that the atoms are $2$-norm dense among unitaries: each unitary is a $2$-norm limit of $\rho(g_j)$ with $g_j$ atoms. Let $f$ be a bounded cocycle of degree $n+1$ such that for each fixed $a\in M^n$, the map $x\mapsto f(a,x)$ has a $2$-norm modulus of continuity on balls (`BallModulus τ.toPreGNS (f.curryRight a)`). Then there is a primitive $g$ of degree $n$ with $\|g\|\le\|f\|$ and $\partial g=f$. Here a cochain of degree $k$ is a bounded complex $k$-linear map $M^k\to M$, and $\partial$ (`differentialValue`) is the Hochschild differential $(\partial f)(v_0,\dots,v_k)=v_0f(v_1,\dots,v_k)+\sum_{j<k}(-1)^{j+1}f(\dots,v_jv_{j+1},\dots)+(-1)^{k+1}f(v_0,\dots,v_{k-1})v_k$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.BoundedHochschild.primitive_of_walk_and_last_modulus`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/BoundedHochschild/PrimitiveAverages.lean#L277

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
open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildRigidity
variable {M X I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

end BoundedHochschild

namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

end BoundedHochschild

open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildRigidity HochschildLiouville TracialUltrapower
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (τ : M →ₚ[ℂ] ℂ) (h1 : τ 1 = 1)
  (htr : ∀ a b : M, τ (a*b)=τ (b*a))

include h1 htr

end BoundedHochschild

open MeasureTheory Filter Topology
open scoped ENNReal
namespace HochschildWalk
variable {G : Type*} [MeasurableSpace G] [MeasurableSingletonClass G]

end HochschildWalk

namespace BoundedHochschild
open HochschildWalk
variable {M : Type*} [CStarAlgebra M]
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableSingletonClass G]

end BoundedHochschild

open MeasureTheory Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildWalk HochschildLiouville TracialUltrapower
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

theorem primitive_of_walk_and_last_modulus
    (h1 : τ 1 = 1) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hR : ∀ b : M, HasPreadjoint e ((ContinuousLinearMap.mul ℂ M).flip b))
    (hτ : TraceInPredual e τ)
    (ρ : G →* unitary M) (p : ℕ → ℝ) (atoms : ℕ → G)
    (hp : ∀ j, 0 ≤ p j) (hs : HasSum p 1)
    (hsym : (atomicLaw p atoms).map (fun g => g⁻¹) = atomicLaw p atoms)
    (time : ℕ → ℕ) (htime : Tendsto time atTop atTop)
    (hmom : FreeMomentsInProbability (atomicLaw p atoms) (fun g => ‖τ (ρ g : M)‖) time)
    (hdense : ∀ u : unitary M, ∃ g : ℕ → G, (∀ j, atomicLaw p atoms {g j} ≠ 0) ∧
      Tendsto (fun j => ‖τ.toPreGNS ((ρ (g j):M)-(u:M))‖) atTop (𝓝 0))
    {n : ℕ} (f : Cochain M (n+1))
    (hf : ∀ x : Fin (n+2) → M, differentialValue f x = 0)
    (hmod : ∀ a : Fin n → M, BallModulus τ.toPreGNS (f.curryRight a)) :
    ∃ g : Cochain M n, ‖g‖ ≤ ‖f‖ ∧ ∀ x, differentialValue g x = f x := by
  sorry

end BoundedHochschild
end
end OAI
