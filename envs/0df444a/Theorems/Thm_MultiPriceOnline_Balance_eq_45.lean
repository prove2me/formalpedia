-- Prove2me | Theorems.Thm_MultiPriceOnline_Balance_eq_45
-- name    : MultiPriceOnline.Balance.eq_45
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:44:04.08045+00:00
-- url     : https://prove2.me/theorems/b41d6fa1-e960-4606-a924-e4b4d7008d29
-- title:
--   (45), App. B.2, p. 44 — the k = 1 procedure ρ_d = σ⁽ᵈ⁾, f_d(1) = r⁽ᵈ⁾/σ⁽¹⁾ satisfies (17)–(18) with c = σ⁽¹⁾/2
-- statement:
--   Let $0<r^{(1)}<\dots<r^{(m)}$ be a price set with $m\ge1$ and let $\sigma^{(1)},\dots,\sigma^{(m)}$ be the values of (8): positive, summing to $1$, with $\sigma^{(1)}=\sigma^{(j)}/(1-r^{(j-1)}/r^{(j)})$. Consider an item with inventory $k=1$. For $d\in[m]$, configuration $d$ has borders $\tilde L^{(0)}=\dots=\tilde L^{(d-1)}=0$ and $\tilde L^{(d)}=\dots=\tilde L^{(m)}=1$. Draw configuration $d$ with probability $\rho_d=\sigma^{(d)}$ and use the value function
--   $$
--   f_d(0)=0,\qquad f_d(1)=\frac{r^{(d)}}{\sigma^{(1)}}.
--   $$
--   This is a randomized procedure, and it satisfies (17) and (18) with
--   $$
--   c=\frac{\sigma^{(1)}}{2}.
--   $$
--
--   This is the solution (45) of the paper's optimization problem (44) for $k=1$. Applied to every unit of a split item, it gives bound (ii), $G(\mathcal P_i)/2$, of Theorem 1.
--
--   **Formalization Note** Only feasibility of (45) for (17)–(18) is posed. The page's further claims, that (45) is the unique solution of the equality system and optimal for (44), are not part of this statement.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, App. B.2, pp. 43–44, (44), (45)

import Mathlib
import Definitions.Def_MultiPriceOnline_Balance_PriceSet
import Definitions.Def_MultiPriceOnline_Balance_Procedure

namespace MultiPriceOnline.Balance

/-- The `k = 1` procedure (45) (Ma–Simchi-Levi, arXiv:1905.04770v1, App. B.2, p. 44): for a price
set `r` with `m ≥ 1` prices and the values `σ` of (8), drawing configuration `d ∈ [m]`
(`L̃⁽⁰⁾ = … = L̃⁽ᵈ⁻¹⁾ = 0`, `L̃⁽ᵈ⁾ = … = L̃⁽ᵐ⁾ = 1`) with probability `ρ_d = σ⁽ᵈ⁾` and using the value
function `f_d(1) = r⁽ᵈ⁾/σ⁽¹⁾` is a randomized procedure for inventory `1` that satisfies (17)–(18)
with `c = σ⁽¹⁾/2`. -/
theorem eq_45 (m : ℕ) (hm : 1 ≤ m) (r σ : ℕ → ℝ) (hr : IsPriceSet m r)
    (hσ : IsBQLimits m r σ) :
    IsProcedure (proc45 m r σ) ∧ Cond17 r (proc45 m r σ) (Gval σ / 2) ∧
    Cond18 r (proc45 m r σ) := by sorry

end MultiPriceOnline.Balance
