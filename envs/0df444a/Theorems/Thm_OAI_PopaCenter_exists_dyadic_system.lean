-- Prove2me | Theorems.Thm_OAI_PopaCenter_exists_dyadic_system
-- name    : OAI.PopaCenter.exists_dyadic_system
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:42:02.6208+00:00
-- url     : https://prove2.me/theorems/f8d75c5a-9529-4e1d-ae57-2a29404156bf
-- title:
--   Dyadic matrix systems in the absence of abelian corners
-- statement:
--   Throughout, $M$ is a unital C*-algebra with a partial order making it star-ordered, $X$ is a complex Banach space, and $e:X^*\to M$ is an isometric conjugate-linear isomorphism, so $M$ is a von Neumann algebra with predual $X$ (the Lean hypothesis `e`). A family $(a_i)$ converges in the predual sense to $b$ (`PredualTendsto`) when $e^{-1}(a_i)(z)\to e^{-1}(b)(z)$ for every $z\in X$. Here $\tau$ is a positive linear functional on $M$ with $\tau(1)=1$ that lies in the predual (`TraceInPredual`: $\tau(x)=\overline{e^{-1}(x)(z)}$ for some $z\in X$), is tracial, and is faithful ($\tau(a^*a)=0$ implies $a=0$), and $\|x\|_2=\tau(x^*x)^{1/2}$ is the norm of `τ.toPreGNS x`. The map $E$ (`average`) sends $a$ to a central element $E(a)$, chosen by `Classical.choose` from `exists_central_average`, with $\|E(a)\|\le\|a\|$ and whose $2$-norm vector lies in the $2$-norm closed convex hull of the unitary conjugates of $a$. A projection $p$ is homogeneous (`Homogeneous`) when $E(p)=\operatorname{Re}\tau(p)\cdot 1$. The hypothesis `NoAbelianCorners M` says that for every nonzero projection $p$ the corner algebra $\{a:pa=a=ap\}$ contains two noncommuting elements. A matrix system of size $n$ under a projection $p$ (`System n p`) is a family $(e_{ij})_{i,j<n}$ in $M$ with $e_{ij}^*=e_{ji}$, $e_{ij}e_{kl}=\delta_{jk}e_{il}$ and $\sum_ie_{ii}=p$. If `NoAbelianCorners M` holds, then for every $k$ there is a matrix system of size $2^k$ under $1$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.PopaCenter.exists_dyadic_system`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/TracialCohomology/Partitions.lean#L248

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

namespace OAI

noncomputable section

open scoped ComplexOrder
namespace PopaMatrices
open BoundedHochschild HochschildRigidity HochschildDiffuse PopaCorners
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
  (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

end PopaMatrices

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaCorners PopaCorners.CornerIso PopaMatrices PopaTypeII
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
include e hτ htr hfaith h1

theorem exists_dyadic_system (hII : NoAbelianCorners M) (k : ℕ) :
    Nonempty (System (2^k) (1:M)) := by
  sorry

end PopaCenter
end
end OAI
