-- Prove2me | Theorems.Thm_OAI_PopaCenter_full_center_lift_norm
-- name    : OAI.PopaCenter.full_center_lift_norm
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:40:57.337388+00:00
-- url     : https://prove2.me/theorems/f0b43ed3-f2fa-4801-8574-0978454f1f3e
-- title:
--   Lifting the center of a homogeneous corner isometrically
-- statement:
--   Throughout, $M$ is a unital C*-algebra with a partial order making it star-ordered, $X$ is a complex Banach space, and $e:X^*\to M$ is an isometric conjugate-linear isomorphism, so $M$ is a von Neumann algebra with predual $X$ (the Lean hypothesis `e`). A family $(a_i)$ converges in the predual sense to $b$ (`PredualTendsto`) when $e^{-1}(a_i)(z)\to e^{-1}(b)(z)$ for every $z\in X$. Here $\tau$ is a positive linear functional on $M$ with $\tau(1)=1$ that lies in the predual (`TraceInPredual`: $\tau(x)=\overline{e^{-1}(x)(z)}$ for some $z\in X$), is tracial, and is faithful ($\tau(a^*a)=0$ implies $a=0$), and $\|x\|_2=\tau(x^*x)^{1/2}$ is the norm of `τ.toPreGNS x`. The map $E$ (`average`) sends $a$ to a central element $E(a)$, chosen by `Classical.choose` from `exists_central_average`, with $\|E(a)\|\le\|a\|$ and whose $2$-norm vector lies in the $2$-norm closed convex hull of the unitary conjugates of $a$. A projection $p$ is homogeneous (`Homogeneous`) when $E(p)=\operatorname{Re}\tau(p)\cdot 1$. The hypothesis `NoAbelianCorners M` says that for every nonzero projection $p$ the corner algebra $\{a:pa=a=ap\}$ contains two noncommuting elements. Assume `NoAbelianCorners M`. Let $p$ be a projection with $E(p)=t\cdot1$, $t>0$, and let $x$ be a central element of the corner algebra of $p$. Then there is a central $c\in M$ with $cp=x$ and $\|c\|=\|x\|$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.PopaCenter.full_center_lift_norm`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/TracialCohomology/CornerTraces.lean#L298

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

namespace OAI

noncomputable section

open scoped ComplexOrder
namespace PopaCorner
open BoundedHochschild HochschildRigidity HochschildDiffuse
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {p : M} (hp : IsStarProjection p) (τ : M →ₚ[ℂ] ℂ)

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

end PopaCorner

open scoped ComplexOrder
namespace PopaCorner
open BoundedHochschild HochschildRigidity HochschildDiffuse PopaMatrices
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable {p : M} (hp : IsStarProjection p)

section Dual
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

end Dual
end PopaCorner

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity HochschildDiffuse PopaTypeII PopaMatrices PopaCorner
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

end PopaCenter

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaCorner
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include h1

theorem full_center_lift_norm (hII : PopaTypeII.NoAbelianCorners M) {p : M}
    (hp : IsStarProjection p) {t : ℝ} (ht : 0<t)
    (hEp : average e τ hτ htr hfaith p=t • (1:M))
    (x : algebra hp) (hx : Central x) :
    ∃ c : M, Central c ∧ c*p=(x:M) ∧ ‖c‖=‖x‖ := by
  sorry

end PopaCenter
end
end OAI
