-- Prove2me | Theorems.Thm_MartOT_Product_strict_convex_integral_eq_iff
-- name    : MartOT.Product.strict_convex_integral_eq_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:21.378778+00:00
-- url     : https://prove2.me/theorems/54f71e67-9bcd-4581-a2f3-394c4e74daa6
-- title:
--   Proof of Theorem 6.3, p. 38 — η ⪯C η′, ψ strictly convex: ∫ψ dη ≤ ∫ψ dη′, with equality iff η = η′
-- statement:
--   Let $\eta,\eta'$ be finite Borel measures on $\mathbb R$ with finite first moments and $\eta\preceq_C\eta'$, and let $\psi:\mathbb R\to\mathbb R$ be strictly convex. Then
--
--   $$\int\psi\,d\eta\le\int\psi\,d\eta',$$
--
--   and, if $\int\psi\,d\eta'<+\infty$,
--
--   $$\int\psi\,d\eta=\int\psi\,d\eta'\quad\Longleftrightarrow\quad\eta=\eta' .$$
--
--   The integrals take values in $(-\infty,+\infty]$ (a convex function is bounded below by an affine one, which is integrable against a measure with finite first moment). The inequality is the definition of the convex order; the content is the equality case: a strictly convex test function detects every strict increase in the convex order. In the proof of Theorem 6.3 it is applied to $\eta=\nu^{\pi_{lc}}_u$ and $\eta'=\nu^\pi_u$.
--
--   **Formalization Note** The integrals are the Setting layer's `integralE`, with values in `EReal`. The finiteness hypothesis $\int\psi\,d\eta'<+\infty$ is not on the page and is necessary: if both integrals are $+\infty$ they are equal without the measures being equal (e.g. $\psi(y)=y^4$, $\eta$ the law of a random variable $X$ with finite mean and $E[X^4]=+\infty$, and $\eta'$ the law of $X+\varepsilon$ with $\varepsilon=\pm1$ a fair sign independent of $X$). The page's $\psi$ is also nonnegative; that is not needed here.
-- source:
--   arXiv:1208.1509v2, §6, proof of Theorem 6.3, p. 38

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Product

open MeasureTheory

/-- Proof of **Theorem 6.3** (p. 38): for `η ⪯C η'` in `𝓜` and a strictly convex `ψ`,
`∫ ψ dη ≤ ∫ ψ dη'`, and when `∫ ψ dη' < +∞` equality holds if and only if `η = η'`. -/
theorem strict_convex_integral_eq_iff (η η' : Measure ℝ) (h : MartOT.Var.ConvexLE η η') (ψ : ℝ → ℝ)
    (hψ : StrictConvexOn ℝ Set.univ ψ) :
    MartOT.Var.integralE η ψ ≤ MartOT.Var.integralE η' ψ ∧
      (MartOT.Var.integralE η' ψ < ⊤ → (MartOT.Var.integralE η ψ = MartOT.Var.integralE η' ψ ↔ η = η')) := by sorry

end MartOT.Product
