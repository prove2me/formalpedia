-- Prove2me | Theorems.Thm_GSCoord_eq_8
-- name    : GSCoord.eq_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:23:55.189252+00:00
-- url     : https://prove2.me/theorems/23107424-7d80-4568-bc9e-f3f5faf5c72e
-- title:
--   (8) — the centralized optimum $\mathbf P$ equals $\min_{S_B\ge0}\mathbf P_1(S_B)+\mathbf P_2(S_B)$
-- statement:
--   Consider a serial supply chain with stages $1,\dots,N$, lead times $T_k$, holding costs $h_k$, average demand $\mu$, demand bound $D$ and boundary service times $s_1$, $s_{N+1}$. Split it between two players: player 1 (downstream) controls stages $1,\dots,N_1$ and player 2 (upstream) controls stages $N_1+1,\dots,N$, where $1\le N_1<N$, and let $S_B=S_{N_1+1}$ be the service time between the players. Let $\mathbf P$ be the optimal value of the global program (6), and $\mathbf P_1(S_B)$, $\mathbf P_2(S_B)$ the optimal values of the two players' programs for a given $S_B$. Then
--
--   $$
--   \mathbf P=\min_{S_B\ge0}\ \mathbf P_1(S_B)+\mathbf P_2(S_B).
--   $$
--
--   That is, there is an integer $S_B\ge0$ with $\mathbf P=\mathbf P_1(S_B)+\mathbf P_2(S_B)$, and $\mathbf P\le\mathbf P_1(S_B)+\mathbf P_2(S_B)$ for every integer $S_B\ge0$. Optimal values are $+\infty$ for infeasible programs.
--
--   If the two players agree on the service time between them that minimizes the sum of their separately optimized costs, the total safety-stock cost of the supply chain is the centralized optimum. This is the paper's basis for the incentive compatibility of the coordination contracts of §3.
--
--   Differences from the source:
--   - reading: service times in a discrete-time model → integer $S_k$, $s_1$, $s_{N+1}$, $S_B$; reason: p.5 "We assume a discrete time model", and $D$ of (2) is defined at integer arguments only
--   - generalization: the demand bound $D$ of (2), concave by the assumption on p.6, holding costs $h_k$, mean demand $\mu$, boundary values $s_1$, $s_{N+1}$ → arbitrary $D:\mathbb Z\to\mathbb R$, real $h_k$, $\mu$, integer $s_1$, $s_{N+1}$ without sign conditions; reason: the argument uses no property of these data, and the paper's data are an instance (feasible points have $\tau_k\ge0$, so the values of $D$ at negative arguments are never read)
--   - reading: $\mathbf P_2(S_B)$ "defined for stages $N_1+1,\dots,N$" with its boundary conditions → rows $S_k-S_{k+1}\le T_k$ for $k\in\{N_1+1,\dots,N\}$, $S_k\ge0$ for $k\in\{N_1+2,\dots,N\}$, objective $\sum_{k=N_1+1}^N$; reason: the page defines $\mathbf P_2$ in words "similar" to (7); this is (7) on player 2's stages
--   - reading: player 1 controls stages $1,\dots,N_1$ and player 2 stages $N_1+1,\dots,N$ → $1\le N_1<N$; reason: each player controls at least one stage
--   - encoding: optimal values of minimization programs → infima in `EReal`, $\top$ for an infeasible program, decision vectors $\mathbb N\to\mathbb Z$ read at $1,\dots,N+1$; reason: Lean convention; same instances
--   - encoding: $\min_{S_B\ge0}$ → `IsLeast` (a least element, attained at some $S_B\ge0$); reason: this is the meaning of min
-- source:
--   Schoenmeyr, Graves, Coordination of multi-echelon supply chains using the guaranteed service framework, SSRN 3243806, §2 "Separation of the problem", (8), p.9 (proof: Appendix II, pp.28–29)

import Mathlib
import Definitions.Def_GSCoord_Model

namespace GSCoord

/-- Display (8) (Schoenmeyr, Graves, Coordination of multi-echelon supply chains using the
guaranteed service framework, SSRN 3243806, §2 "Separation of the problem", (8), p.9; proof in
Appendix II, pp.28–29): for a serial guaranteed-service system split between player 1 (stages
`1, …, N₁`) and player 2 (stages `N₁+1, …, N`),
`P = min_{S_B ≥ 0} P₁(S_B) + P₂(S_B)`.

**Formalization Note.** "min" is stated as `IsLeast`: the optimal value of **P** equals
`P₁(S_B) + P₂(S_B)` for some `S_B ≥ 0` and is at most it for every `S_B ≥ 0`. Optimal values are
infima in `EReal`, `⊤` for an infeasible program. Service times, `s₁`, `s_{N+1}` and `S_B` are
integers (the discrete-time model); `D` is an arbitrary function `ℤ → ℝ` and `h`, `μ`, `s₁`,
`s_{N+1}` carry no sign conditions. `P₂(S_B)`, defined in words on p.7, uses the constraint rows
of (7) on stages `N₁+1, …, N`. `1 ≤ N₁ < N`: both players control at least one stage. -/
theorem eq_8 (sys : SerialSystem) (N₁ : ℕ) (hN₁ : 1 ≤ N₁) (hN₁N : N₁ < sys.N) :
    IsLeast {v : EReal | ∃ SB : ℤ, 0 ≤ SB ∧ v = valP1 sys N₁ SB + valP2 sys N₁ SB}
      (valP sys) := by sorry

end GSCoord
