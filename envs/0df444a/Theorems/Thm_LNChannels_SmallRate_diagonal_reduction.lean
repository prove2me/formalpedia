-- Prove2me | Theorems.Thm_LNChannels_SmallRate_diagonal_reduction
-- name    : LNChannels.SmallRate.diagonal_reduction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T10:59:42.812594+00:00
-- url     : https://prove2.me/theorems/5935b90d-9f42-4e95-bd0c-1784d7d0015c
-- title:
--   Symmetric channel diagonal reduction
-- statement:
--   Let $\alpha>1$ and $B\ge0$. For $x,y>0$ define $G(x,y)=x+y+B(\alpha^x+\alpha^y)/((\alpha^x-1)(\alpha^y-1))$. At $m=(x+y)/2$,
--
--   $$G(m,m)\le G(x,y),\qquad G(m,m)=2m+\frac{2B\alpha^m}{(\alpha^m-1)^2}.$$
--
--   Thus every admissible pair has a diagonal pair of no greater cost. **Formalization Note** This midpoint inequality expresses the paper's diagonal reduction without presupposing that a minimum is attained.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), p. 11 (PDF 12), proof of Theorem 2(ii), paragraph and equation (21)

import Mathlib

set_option autoImplicit false

namespace LNChannels.SmallRate

/-- The diagonal reduction following the symmetric-cost display, p. 11. -/
theorem diagonal_reduction (a B l₁ l₂ : ℝ) (ha : 1 < a) (hB : 0 ≤ B)
    (hl₁ : 0 < l₁) (hl₂ : 0 < l₂) :
    let G : ℝ → ℝ → ℝ := fun x y =>
      x + y + B * (a ^ x + a ^ y) / ((a ^ x - 1) * (a ^ y - 1))
    let m := (l₁ + l₂) / 2
    G m m ≤ G l₁ l₂ ∧
      G m m = 2 * m + 2 * B * a ^ m / (a ^ m - 1) ^ 2 := by sorry

end LNChannels.SmallRate
