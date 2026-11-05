-- Prove2me | Theorems.Thm_OAI_PopaCenter_produced_finite_paths
-- name    : OAI.PopaCenter.produced_finite_paths
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:40:56.776717+00:00
-- url     : https://prove2.me/theorems/049c81fb-e519-4f64-b569-5c862bb3ebcb
-- title:
--   No abelian corners implies the finite path tests
-- statement:
--   Throughout, $M$ is a unital C*-algebra with a partial order making it star-ordered, $X$ is a complex Banach space, and $e:X^*\to M$ is an isometric conjugate-linear isomorphism, so $M$ is a von Neumann algebra with predual $X$ (the Lean hypothesis `e`). A family $(a_i)$ converges in the predual sense to $b$ (`PredualTendsto`) when $e^{-1}(a_i)(z)\to e^{-1}(b)(z)$ for every $z\in X$. Here $\tau$ is a positive linear functional on $M$ with $\tau(1)=1$ that lies in the predual (`TraceInPredual`: $\tau(x)=\overline{e^{-1}(x)(z)}$ for some $z\in X$), is tracial, and is faithful ($\tau(a^*a)=0$ implies $a=0$), and $\|x\|_2=\tau(x^*x)^{1/2}$ is the norm of `τ.toPreGNS x`. The hypothesis `NoAbelianCorners M` says that for every nonzero projection $p$ the corner algebra $\{a:pa=a=ap\}$ contains two noncommuting elements. If `NoAbelianCorners M` holds, then $\tau$ satisfies the finite path tests (`FinitePathTests τ`): given finite types $C,D\neq\emptyset,T$, unitaries $(v_c)_{c\in C}$, for each $t\in T$ a word pattern $w_t$ in $(C\sqcup D)\times\{\pm\}$ in which each row $i$ contains a letter $a_i\in D$ that occurs at exactly one position of the whole array $w_t$, a nontrivial reduced word $q_t$ in the rows, and $\varepsilon>0$, there are unitaries $(u_d)_{d\in D}$ with
--
--   $$\Bigl|\tau\bigl(q_t(\text{row values})\bigr)\Bigr|<\varepsilon\qquad\text{for every }t\in T.$$
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.PopaCenter.produced_finite_paths`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/TracialCohomology/FinitePaths.lean#L87

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

namespace OAI

noncomputable section

open scoped ComplexOrder
namespace MissingFinitePaths
open BoundedHochschild HochschildDiffuse HochschildRare
universe u

end MissingFinitePaths

open scoped ComplexOrder
namespace PopaPatching
open HochschildRare HochschildPaths
variable {C D M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : BoundedHochschild.TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

end PopaPatching

open scoped ComplexOrder
namespace PopaCenter
open PopaPatching HochschildRare HochschildPaths
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : BoundedHochschild.TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
include e hτ htr hfaith h1

theorem produced_finite_paths (hII : PopaTypeII.NoAbelianCorners M) :
    FinitePathTests τ := by
  sorry

end PopaCenter
end
end OAI
