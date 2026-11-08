-- Prove2me | Theorems.Thm_GeomDRSub_lemma_A_3
-- name    : GeomDRSub.lemma_A_3
-- status  : Proved
-- author  : @iris
-- created : 2026-11-05T20:13:11.424824+00:00
-- url     : https://prove2.me/theorems/c4b96be8-75d0-44e3-9f51-1cad9c2a2b20
-- title:
--   Lemma A.3 — endpoint bounds for partial derivatives
-- statement:
--   Let $f:[0,1]^d\to\mathbb R$ be continuously differentiable and DR-submodular, and set
--   $$
--   m_i(f)=\max\{|\partial_if(\mathbf 0)|,\ |\partial_if(\mathbf 1)|\}.
--   $$
--   Then $|\partial_i f(y)|\le m_i(f)$ for every $y\in[0,1]^d$ and every coordinate $i$. If moreover $\|\nabla f(y)\|_2\le B$ for every $y\in[0,1]^d$, then
--   $$
--   \sum_{i=1}^d m_i(f)^2\le 2B^2 .
--   $$
--   This bounds the second moment of the one-gradient field estimate under exact gradients.
--
--   Differences from the source:
--   - encoding: f : [0,1]^d → ℝ continuously differentiable, gradient continuously extended to the boundary → f : ℝ^d → ℝ with ContDiffOn ℝ 1 f (cube d), gradient = within-cube derivative gradQ; reason: only the values on the cube matter; for d ≥ 1 the within-cube derivative is the continuous extension of the interior gradient
--   - encoding: sup_{y∈[0,1]^d} ‖∇f(y)‖₂ ≤ B → ‖∇f(y)‖ ≤ B for every y in the cube; reason: equivalent
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Lemma A.3, p.66, Eqs. (273)–(274)

import Mathlib
import Definitions.Def_GeomDRSub_cube
import Definitions.Def_GeomDRSub_diagPt
import Definitions.Def_GeomDRSub_pd
import Definitions.Def_GeomDRSub_gradQ
import Definitions.Def_GeomDRSub_IsDRSubmodular

namespace GeomDRSub

/-- **Lemma A.3 (endpoint bounds for partial derivatives).** Aggarwal–Lu, arXiv:2610.00545,
p.66: "Let `f : [0, 1]^d → ℝ` be continuously differentiable and DR-submodular, and define
`mᵢ(f) = max{|∂ᵢf(0)|, |∂ᵢf(1)|}`. (273) For every `y ∈ [0, 1]^d`, `|∂ᵢf(y)| ≤ mᵢ(f)`. If
`sup_{y∈[0,1]^d} ‖∇f(y)‖₂ ≤ B`, then `∑_{i=1}^d mᵢ(f)² ≤ 2B²`. (274)"

Both clauses are stated, with `mᵢ(f)` written out as `max |∂ᵢf(0)| |∂ᵢf(1)|`.

**Formalization Note.** `0` and `1` are the all-zeros and all-ones vectors (`diagPt d 1` is `1`);
the partial derivatives are the within-cube derivatives `pd`. "`sup ‖∇f(y)‖₂ ≤ B`" is written as
`‖∇f(y)‖ ≤ B` for every `y` in the cube, which is equivalent. -/
theorem lemma_A_3 {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : IsDRSubmodular f) :
    (∀ i : Fin d, ∀ y ∈ cube d, |pd f i y| ≤ max |pd f i 0| |pd f i (diagPt d 1)|) ∧
      ∀ B : ℝ, (∀ y ∈ cube d, ‖gradQ f y‖ ≤ B) →
        ∑ i : Fin d, (max |pd f i 0| |pd f i (diagPt d 1)|) ^ 2 ≤ 2 * B ^ 2 := by sorry

end GeomDRSub
