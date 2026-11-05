-- Prove2me | Theorems.Thm_OAI_PopaCenter_exists_homogeneous_system
-- name    : OAI.PopaCenter.exists_homogeneous_system
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:42:20.466932+00:00
-- url     : https://prove2.me/theorems/8b0948a6-8b27-4db3-880f-7c5fc1d334e7
-- title:
--   Matrix systems under a homogeneous projection
-- statement:
--   Throughout, $M$ is a unital C*-algebra with a partial order making it star-ordered, $X$ is a complex Banach space, and $e:X^*\to M$ is an isometric conjugate-linear isomorphism, so $M$ is a von Neumann algebra with predual $X$ (the Lean hypothesis `e`). A family $(a_i)$ converges in the predual sense to $b$ (`PredualTendsto`) when $e^{-1}(a_i)(z)\to e^{-1}(b)(z)$ for every $z\in X$. Here $\tau$ is a positive linear functional on $M$ with $\tau(1)=1$ that lies in the predual (`TraceInPredual`: $\tau(x)=\overline{e^{-1}(x)(z)}$ for some $z\in X$), is tracial, and is faithful ($\tau(a^*a)=0$ implies $a=0$), and $\|x\|_2=\tau(x^*x)^{1/2}$ is the norm of `τ.toPreGNS x`. The map $E$ (`average`) sends $a$ to a central element $E(a)$, chosen by `Classical.choose` from `exists_central_average`, with $\|E(a)\|\le\|a\|$ and whose $2$-norm vector lies in the $2$-norm closed convex hull of the unitary conjugates of $a$. A projection $p$ is homogeneous (`Homogeneous`) when $E(p)=\operatorname{Re}\tau(p)\cdot 1$. The hypothesis `NoAbelianCorners M` says that for every nonzero projection $p$ the corner algebra $\{a:pa=a=ap\}$ contains two noncommuting elements. A matrix system of size $n$ under a projection $p$ (`System n p`) is a family $(e_{ij})_{i,j<n}$ in $M$ with $e_{ij}^*=e_{ji}$, $e_{ij}e_{kl}=\delta_{jk}e_{il}$ and $\sum_ie_{ii}=p$. If `NoAbelianCorners M` holds, $n>0$ and $p$ is a homogeneous projection, then there is a matrix system of size $n$ under $p$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.PopaCenter.exists_homogeneous_system`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/TracialCohomology/CentralMatrices.lean#L116

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaCenter
open PopaMatrices PopaCorners.CornerIso PopaPatching
open BoundedHochschild HochschildRigidity HochschildDiffuse PopaTypeII
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
include h1

theorem exists_homogeneous_system (hII : PopaTypeII.NoAbelianCorners M) (n : ℕ) (hn : 0<n)
    {p : M} (hp : IsStarProjection p) (hEp : Homogeneous e τ hτ htr hfaith p) :
    Nonempty (System n p) := by
  sorry

end PopaCenter
end
end OAI
