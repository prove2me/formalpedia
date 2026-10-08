-- Prove2me | Theorems.Thm_OnlineConvexOpt_GamesDuality_weak_duality_v2
-- name    : OnlineConvexOpt.GamesDuality.weak_duality_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:22:07.564926+00:00
-- url     : https://prove2.me/theorems/004d3f4c-ba65-4566-b7ac-963ae11e3e63
-- title:
--   Direction 1 — weak duality $\lambda_C\le\lambda_R$ (corrected game values)
-- statement:
--   **Statement (Direction 1, weak duality).** For any two-player zero-sum game given by a payoff matrix $A\in\mathbb R^{n\times m}$ with $n,m\ge1$,
--   $$\lambda_C(A)=\max_{y\in\Delta_m}\min_{x\in\Delta_n}x^\top Ay\;\le\;\min_{x\in\Delta_n}\max_{y\in\Delta_m}x^\top Ay=\lambda_R(A).$$
--   The book's one-line proof is the max-min $\le$ min-max inequality evaluated at an optimal row strategy $x^\star$.
--
--   **Formalization Note.** The retired statement was *proved* only because both `lambdaR` and `lambdaC` of `OnlineConvexOpt_GamesDuality_Game` collapsed to the junk value $0$ (their `⨅ x ∈ Δn` / `⨆ y ∈ Δm` binders evaluate to $\inf\emptyset=\sup\emptyset=0$ outside the simplex), so the theorem read $0\le0$. The new statement imports `OnlineConvexOpt_GamesDuality_Game_v2`, where $\lambda_R$ and $\lambda_C$ are the real infimum/supremum of the images of the simplices (genuine extrema for $n,m\ge1$). No hypothesis bounds the entries of $A$, as before (the inequality is invariant under scaling and shifting).
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 145, Direction 1 (PDF p. 167)

import Mathlib
import Definitions.Def_OnlineConvexOpt_GamesDuality_Game_v2

namespace OnlineConvexOpt.GamesDuality

/-- **Direction 1** (`λ_R ≥ λ_C`), Hazan, *Introduction to Online Convex Optimization*, 2nd
ed., arXiv:1909.05207v3, p. 145 ("weak duality" in the LP context): for any zero-sum game
given by payoff matrix `A` (with `n, m ≥ 1` pure strategies), the row player's guaranteed loss
`λ_R = min_{x∈Δn} max_{y∈Δm} x⊤Ay` is at least the column player's guaranteed reward
`λ_C = max_{y∈Δm} min_{x∈Δn} x⊤Ay`.

Corrected version: `lambdaR`/`lambdaC` are now the `OnlineConvexOpt_GamesDuality_Game_v2`
values (genuine extrema over the nonempty compact simplices); the retired definitions' nested
`⨅ x ∈ Δn` / `⨆ y ∈ Δm` binders collapsed both to the junk value `0`, so the retired theorem
was provable as `0 ≤ 0` without any game theory. -/
theorem weak_duality_v2 {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (A : Matrix (Fin n) (Fin m) ℝ) :
    lambdaC A ≤ lambdaR A := by sorry

end OnlineConvexOpt.GamesDuality
