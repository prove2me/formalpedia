-- Prove2me | Theorems.Thm_OAI_HochschildFirstLetter_countable_first_letter_rigidity
-- name    : OAI.HochschildFirstLetter.countable_first_letter_rigidity
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:41:49.970906+00:00
-- url     : https://prove2.me/theorems/53fd5052-1e76-4387-950c-b38dae2cf183
-- title:
--   Rigidity of first-letter multipliers over a free family of unitaries
-- statement:
--   Let $A$ be a unital C*-algebra with star-ordered partial order and $\tau$ a faithful tracial positive functional with $\tau(1)=1$. Let $u:F_\infty\to A$ be a group homomorphism from the free group on $\mathbb N$ with $u(g)^*=u(g^{-1})$ and $\tau(u(g))=0$ for $g\ne1$. Let $R:A\to A$ be a bounded linear map that is sequentially continuous for the $2$-norm on bounded sequences: if $(x_r)$ is bounded and $\|x_r\|_2\to0$ then $\|R(x_r)\|_2\to0$. Let $a,b\in A$ with the following property: for every reduced word $g$ with first letter $(i,t)$ and no repeated generator,
--
--   $$R(u(g))=\begin{cases}a\,u(g)&t=\text{true}\\ b\,u(g)&t=\text{false.}\end{cases}$$
--
--   Then $a=b$.
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.HochschildFirstLetter.countable_first_letter_rigidity`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/BoundedHochschild/FirstLetter.lean#L154

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
namespace HochschildFirstLetter
noncomputable section
open Filter Topology
open scoped Polynomial ComplexOrder
open HochschildFreeSums HochschildNewtonPolar HochschildBlockSpan
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem countable_first_letter_rigidity
    (τ : A →ₚ[ℂ] ℂ) (u : FreeGroup ℕ →* A)
    (h1 : τ 1 = 1) (hu : ∀ g, star (u g) = u g⁻¹)
    (hfree : ∀ g, g ≠ 1 → τ (u g) = 0)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (hf : ∀ a : A, τ (star a*a) = 0 → a = 0)
    (R : A →L[ℂ] A)
    (hR : ∀ x : ℕ → A, (∃ C : ℝ, ∀ r, ‖x r‖ ≤ C) →
      Tendsto (fun r => ‖τ.toPreGNS (x r)‖) atTop (nhds 0) →
      Tendsto (fun r => ‖τ.toPreGNS (R (x r))‖) atTop (nhds 0))
    (a b : A)
    (hw : ∀ (g : FreeGroup ℕ) i t l, g.toWord = (i,t)::l →
      (g.toWord.map Prod.fst).Nodup → R (u g) = (if t then a else b)*u g) :
    a = b := by
  sorry

end
end HochschildFirstLetter
end
end OAI
