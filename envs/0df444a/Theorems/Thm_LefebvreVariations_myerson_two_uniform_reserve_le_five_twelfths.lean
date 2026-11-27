-- Prove2me | Theorems.Thm_LefebvreVariations_myerson_two_uniform_reserve_le_five_twelfths
-- name    : LefebvreVariations.myerson_two_uniform_reserve_le_five_twelfths
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T22:20:25.593955+00:00
-- url     : https://prove2.me/theorems/55bf6096-1f5f-5be0-9e7e-f0fb78ae33e5
-- title:
--   Lefebvre's variations, No. 256 — on a theme by Myerson: two uniform bidders in a second-price auction earn at most 5/12 with any reserve price
-- statement:
--   Two bidders have independent values $X,Y$ uniform on $[0,1]$. In a second-price auction with reserve price $r\in[0,1]$ the item is sold if and only if $\max(X,Y)\ge r$, at price $\max(r,\min(X,Y))$. Its expected revenue $R(r)$ satisfies
--   $$R(r)=\int_0^1\!\!\int_0^1 \mathbf 1_{\max(x,y)\ge r}\,\max\big(r,\min(x,y)\big)\,dy\,dx\ \le\ \frac5{12}\quad\text{for all } r\in[0,1],\qquad R\!\left(\tfrac12\right)=\frac5{12}.$$
--
--   Explicitly $R(r)=\tfrac13+r^2-\tfrac43r^3$, which is maximal at $r=\tfrac12$, the monopoly reserve of the uniform distribution (the point where the virtual value $2v-1$ vanishes). This is the simplest case of Myerson's optimal auction: the optimal reserve beats the no-reserve revenue $\tfrac13$.
--
--   **Formalization Note** The revenue is written as an iterated interval integral of the piecewise integrand \texttt{if r $\le$ max x y then (if r $\le$ min x y then min x y else r) else 0}. Ties between the two values or with $r$ have measure zero and do not affect the integrals.
--
--   **Why this is a variation.** Textbook special case in the spirit of Myerson's optimal auction (the platform problem MyersonAuction.Optimal.lemma_3, open, is stated for finite-type environments): two bidders, uniform values, a second-price auction with one reserve price. The statement computes the revenue by double integrals and shows the Myerson reserve 1/2 is optimal among reserves, with revenue 5/12. It is self-contained and is neither a special case of, nor implied by, the parent or the proved MyersonAuction.Optimal.optimal_auction_theorem (different, discrete formalization). No formal link is claimed.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   R. B. Myerson, "Optimal auction design", Math. Oper. Res. 6 (1981), 58-73: the optimal reserve price for a regular distribution solves virtual value = 0, giving 1/2 for the uniform distribution (cited from memory). The closed form R(r) = 1/3 + r^2 - 4r^3/3 is an elementary computation, derived here by hand and numerically on a 1500x1500 grid at seven values of r.

import Mathlib

namespace LefebvreVariations

/-- Two bidders with independent values uniform on `[0,1]` face a second-price auction with
reserve price `r`: the item is sold iff the larger value is at least `r`, at price `max r (smaller
value)`. The expected revenue is `1/3 + r² − 4r³/3`, so no reserve in `[0,1]` earns more than
`5/12`, and the reserve `1/2` earns exactly `5/12`. Source: Myerson, *Optimal auction design*,
Math. Oper. Res. 6 (1981): the optimal reserve for uniform values is `1/2`; the figure `5/12` is a
direct computation. -/
theorem myerson_two_uniform_reserve_le_five_twelfths :
    (∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 →
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        (if r ≤ max x y then (if r ≤ min x y then min x y else r) else 0) ≤ 5 / 12) ∧
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        (if (1 / 2 : ℝ) ≤ max x y then (if (1 / 2 : ℝ) ≤ min x y then min x y else 1 / 2) else 0)
      = 5 / 12 := by
  sorry

end LefebvreVariations
