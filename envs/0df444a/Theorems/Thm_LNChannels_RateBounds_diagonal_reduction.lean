-- Prove2me | Theorems.Thm_LNChannels_RateBounds_diagonal_reduction
-- name    : LNChannels.RateBounds.diagonal_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:44.462832+00:00
-- url     : https://prove2.me/theorems/1a005dd6-80db-41d1-a095-f0be2aa61e1b
-- title:
--   Eq. (21), p. 11 — the excess cost of a symmetric channel is no smaller than at equal sizes $l_1=l_2=(l_1+l_2)/2$
-- statement:
--   Let $\alpha>1$, $B\ge0$, $C\in\mathbb R$, and consider for real $x,y>0$
--   $$H(x,y)=x+y+\frac{B(\alpha^{x}+\alpha^{y})}{(\alpha^{x}-1)(\alpha^{y}-1)}-\frac{2C\alpha}{(\alpha-1)^2}.$$
--   For all real $l_1,l_2>0$, with $m=(l_1+l_2)/2$,
--   $$H(m,m)\le H(l_1,l_2)\qquad\text{and}\qquad H(m,m)=2m+\frac{2B\alpha^{m}}{(\alpha^{m}-1)^2}-\frac{2C\alpha}{(\alpha-1)^2}.\tag{21}$$
--
--   By the previous milestone, $H(l_1,l_2)$ is the cost of a symmetric bidirectional channel minus the on-chain cost $2C\lambda/r$. Hence a symmetric channel is cheaper than on-chain settlement for some sizes only if it is for some equal sizes, and the two-variable problem reduces to the one-variable function (21).
--
--   **Formalization Note** The paper argues that $H$ is strictly convex and symmetric, so its minimizer is unique and lies on the diagonal. That argument presupposes that a minimizer exists. The statement here is the midpoint form, which needs no minimizer: the value at the midpoint of $(l_1,l_2)$ and $(l_2,l_1)$ is no larger than at either point. It is exactly what the proof of Theorem 2(ii) uses.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), DOI 10.1287/mnsc.2022.01664, p. 11 (PDF p. 12), proof of Theorem 2(ii), eq. (21)

import Mathlib
import Definitions.Def_LNChannels_RateBounds_ClosedForms

namespace LNChannels.RateBounds

/-- (21), p. 11, midpoint form: for `α > 1`, `B ≥ 0` and real sizes `l₁, l₂ > 0`, the function
`H(x, y) = x + y + B(α^x + α^y)/((α^x − 1)(α^y − 1)) − 2Cα/(α − 1)²` satisfies
`H(m, m) ≤ H(l₁, l₂)` at `m = (l₁ + l₂)/2`, and `H(m, m) = 2m + 2Bα^m/(α^m − 1)² − 2Cα/(α − 1)²`. -/
theorem diagonal_reduction (α B C l₁ l₂ : ℝ) (hα : 1 < α) (hB : 0 ≤ B) (hl₁ : 0 < l₁)
    (hl₂ : 0 < l₂) :
    let H : ℝ → ℝ → ℝ := fun x y =>
      x + y + B * (α ^ x + α ^ y) / ((α ^ x - 1) * (α ^ y - 1)) - 2 * C * α / (α - 1) ^ 2
    let m := (l₁ + l₂) / 2
    H m m ≤ H l₁ l₂ ∧
      H m m = 2 * m + 2 * B * α ^ m / (α ^ m - 1) ^ 2 - 2 * C * α / (α - 1) ^ 2 := by sorry

end LNChannels.RateBounds
