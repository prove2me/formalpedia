-- Prove2me | Theorems.Thm_HubSpokePricing_Lagrangian_proposition_3_1
-- name    : HubSpokePricing.Lagrangian.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:26.747734+00:00
-- url     : https://prove2.me/theorems/caa93c9f-fcc2-45c9-afb9-b54a7f4d9276
-- title:
--   Proposition 3.1, pp. 11–12 — the relaxation value V̄^λ is independent of the initial state, equals mλ + Σ_i h_i^λ, and is ≥ V^OPT
-- statement:
--   Throughout, $N$ is a hub-and-spoke network with one hub (location $0$), $n\ge 1$ spokes and $m$ resources. A request is of type $(i,0)$ (spoke $i$ to hub) with probability $q_{i0}>0$ and of type $(0,i)$ (hub to spoke $i$) with probability $q_{0i}>0$, these probabilities summing to one; $r_{i0},r_{0i}$ are the one-period expected revenue functions of the demand level $d\in[0,1]$, satisfying Assumption 2.1 with constants $\bar r,\bar\omega>0$.
--
--   For every dual variable $\lambda\ge0$, let $\bar V^\lambda_{(3)}(x^0)$ be the optimal long-run average of revenue plus the Lagrangian reward $\lambda(m-\sum_i x_{i,t})$ in the Lagrangian relaxation (3) from an initial spoke state $x^0\in\bar{\mathcal X}=\{x\in\mathbb N^n:x_i\le m\ \forall i\}$, where the hub level may become negative. Then $\bar V^\lambda_{(3)}(x^0)$ does not depend on $x^0$, decomposes over spokes, and bounds $V^{\mathrm{OPT}}$:
--   $$\bar V^\lambda_{(3)}(x^0)\;=\;m\lambda+\sum_{i=1}^n h_i^\lambda\quad(x^0\in\bar{\mathcal X}),\qquad V^{\mathrm{OPT}}(x^0)\;\le\;\bar V^\lambda_{(3)}(x^0)\quad(x^0\in\mathcal X),$$
--   where $V^{\mathrm{OPT}}(x^0)$ is the optimal long-run average revenue of problem (1) from $x^0$ and $h_i^\lambda$ is the optimal value of the spoke problem (6).
--
--   The Lagrangian relaxation drops the hub's non-negativity constraint and charges $\lambda$ per resource per period held in the spokes; it then decouples over spokes into the decomposition (4). The upper bound is the second inequality of Theorem 4.1.
--
--   **Formalization Note** $h_i^\lambda$ is defined as the optimal value of (6); the paper defines it as the spoke DP's optimal average revenue and identifies the two in Proposition 3.2. The Bellman equation (5) is stated in the item for Proposition 3.2 (the value of (6) together with differential value functions solves (5)). Both $V^{\mathrm{OPT}}$ and the relaxation's value use a `limsup` of finite-horizon averages (the paper writes $\lim$) over deterministic history-dependent feasible policies.
-- source:
--   Balseiro, Brown & Chen, Dynamic Pricing of Relocating Resources in Large Networks, SSRN 3313737 (version of May 23, 2020), https://ssrn.com/abstract=3313737, pp. 11–12, Proposition 3.1, (3), (4)

import Mathlib
import Definitions.Def_HubSpokePricing_Lagrangian_Model

namespace HubSpokePricing.Lagrangian

/-- Proposition 3.1 (pp. 11–12): for every `λ ≥ 0` the optimal average revenue `V̄^λ` of the
Lagrangian relaxation (3) is independent of the initial state in `𝒳̄` and decomposes over spokes
as `V̄^λ = mλ + ∑ᵢ h_i^λ`, (4) (with `h_i^λ` the optimal value of (6), Proposition 3.2), and it is
an upper bound on `V^OPT` from every initial state in `𝒳`. The Bellman equation (5) is
`proposition_3_2`. -/
theorem proposition_3_1 (N : Network) (hN : N.Standing) (lam : ℝ) (hlam : 0 ≤ lam) :
    (∀ x0 : Fin N.n → ℕ, InXbar N x0 → VbarRelax N lam x0 = Vbar N lam) ∧
      ∀ x0 : Fin N.n → ℕ, InX N x0 → VOPT N x0 ≤ VbarRelax N lam x0 := by sorry

end HubSpokePricing.Lagrangian
