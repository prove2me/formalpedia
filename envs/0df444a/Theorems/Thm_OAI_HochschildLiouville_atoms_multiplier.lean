-- Prove2me | Theorems.Thm_OAI_HochschildLiouville_atoms_multiplier
-- name    : OAI.HochschildLiouville.atoms_multiplier
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:42:32.609778+00:00
-- url     : https://prove2.me/theorems/93dd7938-de3a-49fa-ae8a-b8b406fc2f42
-- title:
--   A Liouville property: harmonic maps on the walk are multipliers on atoms
-- statement:
--   Let $A$ be a unital C*-algebra with a faithful tracial positive functional $\tau$, $\tau(1)=1$. Let $G$ be a countable group with measurable singletons, $\rho:G\to U(A)$ a homomorphism, $R:A\to A$ bounded linear, and $\mu$ a symmetric probability measure on $G$. Assume $R$ is sequentially $2$-norm continuous on bounded sequences (`BallSequential`), and assume free moments in probability along times $t(k)\to\infty$ (`FreeMomentsInProbability`): for each nontrivial word $q$ in $r$ letters and $\delta>0$, the probability that $|\tau(\rho(q(w_1,\dots,w_r)))|\ge\delta$ for independent $\mu$-walk segments of length $t(k)$ tends to $0$. Let $D(g)$ be the image in the GNS space of $R(\rho(g))\rho(g)^{-1}$ (`hilbertD`), and suppose $D$ is $\mu$-harmonic: $\int D(gu)\,d\mu(u)=D(g)$. Then for every atom $g$ of $\mu$,
--
--   $$R(\rho(g))=R(1)\rho(g).$$
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.HochschildLiouville.atoms_multiplier`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/BoundedHochschild/Liouville.lean#L323

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
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
namespace HochschildLiouville
open HochschildRigidity HochschildWalk HochschildFirstLetter TracialUltrapower
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1)
variable (htr : ∀ a b : A, τ (a*b) = τ (b*a))

variable {G : Type*} [Group G]
variable (ρ : G →* unitary A) (R : A →L[ℂ] A)

variable [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
variable (μ : Measure G) [IsProbabilityMeasure μ]

include htr

end HochschildLiouville

open MeasureTheory Filter Topology TopologicalSpace
namespace HochschildProbability

end HochschildProbability

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ENNReal
namespace HochschildWalk
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
variable (μ : Measure G) [IsProbabilityMeasure μ]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

end HochschildWalk

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
namespace HochschildLiouville
open HochschildRigidity HochschildWalk HochschildFirstLetter TracialUltrapower
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1 = 1)
variable (htr : ∀ a b : A, τ (a*b) = τ (b*a))
variable (hf : ∀ x : A, τ (star x * x) = 0 → x = 0)
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
variable (ρ : G →* unitary A) (R : A →L[ℂ] A)
variable (μ : Measure G) [IsProbabilityMeasure μ]

include htr hf

theorem atoms_multiplier (hR : BallSequential τ.toPreGNS R)
    (hsym : μ.map (fun g => g⁻¹) = μ)
    (time : ℕ → ℕ) (htime : Tendsto time atTop atTop)
    (hmom : FreeMomentsInProbability μ (fun g => ‖τ (ρ g : A)‖) time)
    (hh : ∀ g, ∫ u, hilbertD τ h1 ρ R (g*u) ∂μ = hilbertD τ h1 ρ R g) :
    ∀ g, μ {g} ≠ 0 → R (ρ g : A) = R 1 * (ρ g : A) := by
  sorry

end HochschildLiouville
end
end OAI
