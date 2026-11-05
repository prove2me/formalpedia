-- Prove2me | Theorems.Thm_OAI_PopaCenter_exists_matrix_energy_decrease_center
-- name    : OAI.PopaCenter.exists_matrix_energy_decrease_center
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:41:37.28299+00:00
-- url     : https://prove2.me/theorems/ad551742-5b37-4784-85c3-5978d13db168
-- title:
--   One matrix system decreases the 2-norm energy of a central-free element
-- statement:
--   Throughout, $M$ is a unital C*-algebra with a partial order making it star-ordered, $X$ is a complex Banach space, and $e:X^*\to M$ is an isometric conjugate-linear isomorphism, so $M$ is a von Neumann algebra with predual $X$ (the Lean hypothesis `e`). A family $(a_i)$ converges in the predual sense to $b$ (`PredualTendsto`) when $e^{-1}(a_i)(z)\to e^{-1}(b)(z)$ for every $z\in X$. Here $\tau$ is a positive linear functional on $M$ with $\tau(1)=1$ that lies in the predual (`TraceInPredual`: $\tau(x)=\overline{e^{-1}(x)(z)}$ for some $z\in X$), is tracial, and is faithful ($\tau(a^*a)=0$ implies $a=0$), and $\|x\|_2=\tau(x^*x)^{1/2}$ is the norm of `τ.toPreGNS x`. The map $E$ (`average`) sends $a$ to a central element $E(a)$, chosen by `Classical.choose` from `exists_central_average`, with $\|E(a)\|\le\|a\|$ and whose $2$-norm vector lies in the $2$-norm closed convex hull of the unitary conjugates of $a$. A projection $p$ is homogeneous (`Homogeneous`) when $E(p)=\operatorname{Re}\tau(p)\cdot 1$. The hypothesis `NoAbelianCorners M` says that for every nonzero projection $p$ the corner algebra $\{a:pa=a=ap\}$ contains two noncommuting elements. For a matrix system $s$ of size $n$ under $1$, write $s.\mathrm{expect}(b)$ for its averaged expectation (`System.expect`). If `NoAbelianCorners M` holds, $E(b)=0$ and $\|b\|_2>0$, then there is $n>0$ and a matrix system $s$ of size $n$ under $1$ with
--
--   $$\|s.\mathrm{expect}(b)\|_2^2<\Bigl(1-\frac1{1024}\Bigr)\|b\|_2^2.$$
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.PopaCenter.exists_matrix_energy_decrease_center`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/TracialCohomology/CenterExtensions.lean#L288

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaTypeII PopaMatrices
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
variable {n : ℕ} (s : PopaMatrices.System n (1:M))
variable (P : X →L⋆[ℂ] X) (hP : ∀ a z, e.symm (star a) z=star (e.symm a (P z)))

end PopaCenter

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaCorners PopaCorners.CornerIso PopaMatrices
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

namespace System
variable {n : ℕ} (s : PopaMatrices.System n (1:M))

end System
end PopaCenter

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaMatrices PopaTypeII PopaCorners PopaCorners.CornerIso
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

end PopaCenter

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity HochschildDixmier PopaQuantization PopaTypeII PopaMatrices
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

variable (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
include e hτ htr hfaith h1

theorem exists_matrix_energy_decrease_center (hII : NoAbelianCorners M)
    (b : M) (hbτ : average e τ hτ htr hfaith b=0) (hb : 0 < ‖τ.toPreGNS b‖) :
    ∃ n : ℕ, 0 < n ∧ ∃ s : System n (1:M),
      ‖τ.toPreGNS (s.expect b)‖^2 < (1-1/1024:ℝ)*‖τ.toPreGNS b‖^2 := by
  sorry

end PopaCenter
end
end OAI
