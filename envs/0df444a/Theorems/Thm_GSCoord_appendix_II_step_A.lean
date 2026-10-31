-- Prove2me | Theorems.Thm_GSCoord_appendix_II_step_A
-- name    : GSCoord.appendix_II_step_A
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:23:54.635994+00:00
-- url     : https://prove2.me/theorems/cb5661e9-877d-4b0a-be3b-26dd7977d224
-- title:
--   Appendix II, step (A) — $\mathbf P_1(S_B)+\mathbf P_2(S_B)$ equals the merged program with fixed $S_B$
-- statement:
--   Consider a serial guaranteed-service system with stages $1,\dots,N$, split so that player 1 controls stages $1,\dots,N_1$ and player 2 controls stages $N_1+1,\dots,N$, where $1\le N_1<N$. For every integer service time $S_B$ between the players,
--
--   $$
--   \mathbf P_1(S_B)+\mathbf P_2(S_B)\;=\;\min_{S_2,\dots,S_N}\Bigl\{\sum_{k=1}^{N}h_k\bigl(D(S_{k+1}+T_k-S_k)-(S_{k+1}+T_k-S_k)\mu\bigr)\ :\ \begin{array}{l}S_k-S_{k+1}\le T_k,\ k\in\{1,\dots,N\},\\ S_1=s_1,\ S_{N_1+1}=S_B,\ S_{N+1}=s_{N+1},\\ S_k\ge0,\ k\in\{2,\dots,N_1\}\cup\{N_1+2,\dots,N\}\end{array}\Bigr\},
--   $$
--
--   where each optimal value is $+\infty$ for an infeasible program.
--
--   For a fixed $S_B$ the two players' programs share no decision variable, and the objective of $\mathbf P$ splits into the stages of player 1 and those of player 2. This is the first of the three equalities that prove (8).
--
--   Differences from the source:
--   - reading: Appendix II's displays impose $S_k\ge0$ for $k\in\{1,\dots,N_1\}$, $\{N_1+1,\dots,N+1\}$ and $\{1,\dots,N+1\}$ → the §2 index sets $\{2,\dots,N_1\}$, $\{N_1+2,\dots,N\}$ and their union; reason: $\mathbf P_1$, $\mathbf P_2$ are defined in §2 by (7) and p.7, and (8) is about those programs; Appendix II's sets would also constrain the fixed values $s_1$, $S_B$, $s_{N+1}$
--   - generalization: $S_B$ inside $\min_{S_B\ge0}$ → every integer $S_B$; reason: the page states step (A) "for a given $S_B$"; the case $S_B\ge0$ is a special case
--   - reading: the first row of $\mathbf P_1$ on p.28 prints "for $j\in\{1,2,\dots,N_1\}$" and $\mathbf P_2$ prints $\min_{S_{N_1+1},\dots,S_N}$ → the row indexed by $k$, and $S_{N_1+1}$ pinned to $S_B$; reason: the row's formula uses $k$, and the program's own constraint fixes $S_{N_1+1}=S_B$, so neither changes the program
--   - reading: service times in a discrete-time model → integer $S_k$, $s_1$, $s_{N+1}$, $S_B$; reason: p.5 "We assume a discrete time model", and $D$ of (2) is defined at integer arguments only
--   - generalization: the demand bound $D$ of (2), concave by the assumption on p.6, holding costs $h_k$, mean demand $\mu$, boundary values $s_1$, $s_{N+1}$ → arbitrary $D:\mathbb Z\to\mathbb R$, real $h_k$, $\mu$, integer $s_1$, $s_{N+1}$ without sign conditions; reason: the argument uses no property of these data, and the paper's data are an instance (feasible points have $\tau_k\ge0$, so the values of $D$ at negative arguments are never read)
--   - reading: $\mathbf P_2(S_B)$ "defined for stages $N_1+1,\dots,N$" with its boundary conditions → rows $S_k-S_{k+1}\le T_k$ for $k\in\{N_1+1,\dots,N\}$, $S_k\ge0$ for $k\in\{N_1+2,\dots,N\}$, objective $\sum_{k=N_1+1}^N$; reason: the page defines $\mathbf P_2$ in words "similar" to (7); this is (7) on player 2's stages
--   - reading: player 1 controls stages $1,\dots,N_1$ and player 2 stages $N_1+1,\dots,N$ → $1\le N_1<N$; reason: each player controls at least one stage
--   - encoding: optimal values of minimization programs → infima in `EReal`, $\top$ for an infeasible program, decision vectors $\mathbb N\to\mathbb Z$ read at $1,\dots,N+1$; reason: Lean convention; same instances
-- source:
--   Schoenmeyr, Graves, Coordination of multi-echelon supply chains using the guaranteed service framework, SSRN 3243806, Appendix II, step (A), p.28 (justification pp.28–29)

import Mathlib
import Definitions.Def_GSCoord_Model

namespace GSCoord

/-- Appendix II, step (A) (Schoenmeyr, Graves, Coordination of multi-echelon supply chains using
the guaranteed service framework, SSRN 3243806, Appendix II, step (A), p.28): for a given service
time `S_B` between the players, the sum of the optimal values of player 1's program `P₁(S_B)` (7)
and player 2's program `P₂(S_B)` equals the optimal value of the merged program over stages
`1, …, N` with the three boundary conditions `S₁ = s₁`, `S_{N₁+1} = S_B`, `S_{N+1} = s_{N+1}`.
"Step (A) holds, because for a given `S_B`, the two programs are independent of each other."

**Formalization Note.** Stated for every integer `S_B`, not only `S_B ≥ 0`. Optimal values are
infima in `EReal`, `⊤` for an infeasible program. Non-negativity follows the §2 index sets of
(6)–(7) (free variables only), not the sets `{1, …, N₁}`, `{N₁+1, …, N+1}`, `{1, …, N+1}` printed
in Appendix II. `1 ≤ N₁ < N`: both players control at least one stage. -/
theorem appendix_II_step_A (sys : SerialSystem) (N₁ : ℕ) (hN₁ : 1 ≤ N₁) (hN₁N : N₁ < sys.N)
    (SB : ℤ) :
    valP1 sys N₁ SB + valP2 sys N₁ SB = valFix sys N₁ SB := by sorry

end GSCoord
