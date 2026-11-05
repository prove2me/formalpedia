-- Prove2me | Theorems.Thm_OAI_PopaCenter_quantize_words
-- name    : OAI.PopaCenter.quantize_words
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:41:51.465486+00:00
-- url     : https://prove2.me/theorems/9949e8d6-474f-44ec-ab6d-a040a882f22a
-- title:
--   Quantization of finitely many words under a homogeneous projection
-- statement:
--   Throughout, $M$ is a unital C*-algebra with a partial order making it star-ordered, $X$ is a complex Banach space, and $e:X^*\to M$ is an isometric conjugate-linear isomorphism, so $M$ is a von Neumann algebra with predual $X$ (the Lean hypothesis `e`). A family $(a_i)$ converges in the predual sense to $b$ (`PredualTendsto`) when $e^{-1}(a_i)(z)\to e^{-1}(b)(z)$ for every $z\in X$. Here $\tau$ is a positive linear functional on $M$ with $\tau(1)=1$ that lies in the predual (`TraceInPredual`: $\tau(x)=\overline{e^{-1}(x)(z)}$ for some $z\in X$), is tracial, and is faithful ($\tau(a^*a)=0$ implies $a=0$), and $\|x\|_2=\tau(x^*x)^{1/2}$ is the norm of `τ.toPreGNS x`. The map $E$ (`average`) sends $a$ to a central element $E(a)$, chosen by `Classical.choose` from `exists_central_average`, with $\|E(a)\|\le\|a\|$ and whose $2$-norm vector lies in the $2$-norm closed convex hull of the unitary conjugates of $a$. A projection $p$ is homogeneous (`Homogeneous`) when $E(p)=\operatorname{Re}\tau(p)\cdot 1$. The hypothesis `NoAbelianCorners M` says that for every nonzero projection $p$ the corner algebra $\{a:pa=a=ap\}$ contains two noncommuting elements. Let $C,B$ be finite sets, $G$ a group, $v:G\to M$ a map with $v(gh)=v(g)v(h)$ and $v(g^{-1})=v(g)^*$ (`Rep G M`), $a:C\to M$ and $\gamma:B\to G$. A word $l$ in the letters $C\sqcup B$ is evaluated by the product of its letters (`evaluate a γ v l`), with $c\mapsto a_c$ and $b\mapsto v(\gamma_b)$. Assume `NoAbelianCorners M`, let $p\ne0$ be a homogeneous projection, and take $L\in\mathbb N$, $\theta,d>0$. Then there is a nonzero homogeneous projection $q\le p$ with $\operatorname{Re}\tau(q)<d\operatorname{Re}\tau(p)$ such that for all words $l$ of length at most $L$,
--
--   $$\bigl\|q\,w\,q-q\,c(w)\,q\bigr\|_{2,q}\le\theta,\qquad w=\operatorname{ev}(l),$$
--
--   where $\|\cdot\|_{2,q}$ is the $2$-norm of the normalized trace on the corner of $q$ (`PopaCorner.trace`) and $c(w)=\operatorname{Re}\tau(p)^{-1}E(pwp)$ (`cornerCoefficient`).
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.PopaCenter.quantize_words`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/TracialCohomology/WordQuantization.lean#L47

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

namespace OAI

noncomputable section

open scoped ComplexOrder
namespace PopaPatching
universe u v
variable {A : Type u} [Fintype A]

variable {C B : Type u} [Fintype C] [Fintype B]
variable {G : Type u} [Group G]
variable {M X : Type v} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : BoundedHochschild.TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1:M))

end PopaPatching

open scoped ComplexOrder
namespace PopaCenter
open PopaPatching
universe u v
variable {C B : Type u} [Fintype C] [Fintype B]
variable {G : Type u} [Group G]
variable {M X : Type v} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : BoundedHochschild.TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
include h1

theorem quantize_words (hII : PopaTypeII.NoAbelianCorners M)
    {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) (hEp : Homogeneous e τ hτ htr hfaith p)
    (a : C → M) (γ : B → G) (v : Rep G M) (L : ℕ)
    (θ d : ℝ) (hθ : 0<θ) (hd : 0<d) :
    ∃ q : M, ∃ hq : IsStarProjection q, q ≠ 0 ∧ q ≤ p ∧ (τ q).re < d*(τ p).re ∧ Homogeneous e τ hτ htr hfaith q ∧
      ∀ l : List (Letter C B), l.length ≤ L →
        ‖(PopaCorner.trace hq τ).toPreGNS (PopaCorner.compress hq (evaluate a γ v l)-
          PopaCorner.compress hq (cornerCoefficient e τ hτ htr hfaith hp (evaluate a γ v l)))‖≤θ := by
  sorry

end PopaCenter
end
end OAI
