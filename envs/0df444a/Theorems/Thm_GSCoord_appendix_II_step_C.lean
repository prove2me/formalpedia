-- Prove2me | Theorems.Thm_GSCoord_appendix_II_step_C
-- name    : GSCoord.appendix_II_step_C
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:23:55.993698+00:00
-- url     : https://prove2.me/theorems/2ccb02a0-bafa-4c48-a6c5-6c84a679069b
-- title:
--   Appendix II, step (C) — removing the redundant variable $S_B$ gives $\mathbf P$
-- statement:
--   In the setting of (8), with $1\le N_1<N$, the optimal value of the single program in the variables $S_2,\dots,S_N;S_B$,
--
--   $$
--   \min_{S_2,\dots,S_N;\,S_B}\Bigl\{\sum_{k=1}^{N}h_k\bigl(D(\tau_k)-\tau_k\mu\bigr) : S_k-S_{k+1}\le T_k\ (k\le N),\ S_1=s_1,\ S_{N_1+1}=S_B,\ S_{N+1}=s_{N+1},\ S_k\ge0\ (k\in\{2,\dots,N_1\}\cup\{N_1+2,\dots,N\}),\ S_B\ge0\Bigr\},
--   $$
--
--   with $\tau_k=S_{k+1}+T_k-S_k$, equals the optimal value of the global program $\mathbf P$ (6). Optimal values are $+\infty$ for infeasible programs.
--
--   The variable $S_B$ is always equal to $S_{N_1+1}$ and carries no constraint beyond $S_B\ge0$, which is the non-negativity of $S_{N_1+1}$ in $\mathbf P$. This is the last of the three equalities that prove (8).
--
--   Differences from the source:
--   - reading: Appendix II's displays impose $S_k\ge0$ for $k\in\{1,\dots,N+1\}$ on both programs → the §2 index sets: $\{2,\dots,N_1\}\cup\{N_1+2,\dots,N\}$ and $S_B\ge0$ on the joint program, $\{2,\dots,N\}$ on $\mathbf P$ as in (6); reason: $\mathbf P$ is defined in §2 by (6), and (8) is about it; Appendix II's set would also constrain the fixed values $s_1$, $s_{N+1}$
--   - reading: service times in a discrete-time model → integer $S_k$, $s_1$, $s_{N+1}$, $S_B$; reason: p.5 "We assume a discrete time model", and $D$ of (2) is defined at integer arguments only
--   - generalization: the demand bound $D$ of (2), concave by the assumption on p.6, holding costs $h_k$, mean demand $\mu$, boundary values $s_1$, $s_{N+1}$ → arbitrary $D:\mathbb Z\to\mathbb R$, real $h_k$, $\mu$, integer $s_1$, $s_{N+1}$ without sign conditions; reason: the argument uses no property of these data, and the paper's data are an instance (feasible points have $\tau_k\ge0$, so the values of $D$ at negative arguments are never read)
--   - reading: player 1 controls stages $1,\dots,N_1$ and player 2 stages $N_1+1,\dots,N$ → $1\le N_1<N$; reason: each player controls at least one stage
--   - encoding: optimal values of minimization programs → infima in `EReal`, $\top$ for an infeasible program, decision vectors $\mathbb N\to\mathbb Z$ read at $1,\dots,N+1$; reason: Lean convention; same instances
-- source:
--   Schoenmeyr, Graves, Coordination of multi-echelon supply chains using the guaranteed service framework, SSRN 3243806, Appendix II, step (C), pp.28–29

import Mathlib
import Definitions.Def_GSCoord_Model

namespace GSCoord

/-- Appendix II, step (C) (Schoenmeyr, Graves, Coordination of multi-echelon supply chains using
the guaranteed service framework, SSRN 3243806, Appendix II, step (C), pp.28–29): the optimal
value of the single program in the variables `S₂, …, S_N; S_B` equals the optimal value of the
global program **P** (6). "We identify the variable `S_B` as redundant (because it is always equal
to `S_{N₁+1}`, and has no additional constraints), and remove it."

**Formalization Note.** Optimal values are infima in `EReal`, `⊤` for an infeasible program.
Non-negativity follows the §2 index sets of (6)–(7). `1 ≤ N₁ < N`: both players control at least
one stage. -/
theorem appendix_II_step_C (sys : SerialSystem) (N₁ : ℕ) (hN₁ : 1 ≤ N₁) (hN₁N : N₁ < sys.N) :
    valJoint sys N₁ = valP sys := by sorry

end GSCoord
