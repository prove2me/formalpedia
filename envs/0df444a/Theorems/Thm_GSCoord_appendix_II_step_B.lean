-- Prove2me | Theorems.Thm_GSCoord_appendix_II_step_B
-- name    : GSCoord.appendix_II_step_B
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:23:52.913033+00:00
-- url     : https://prove2.me/theorems/b50fff32-ffee-4325-a2d4-e472d1e137cf
-- title:
--   Appendix II, step (B) — the minimum over $S_B\ge0$ of the merged program is the joint program
-- statement:
--   In the setting of (8), with $1\le N_1<N$, let $V(S_B)$ be the optimal value of the merged program with fixed split $S_B$,
--
--   $$
--   V(S_B)=\min_{S_2,\dots,S_N}\Bigl\{\sum_{k=1}^{N}h_k\bigl(D(\tau_k)-\tau_k\mu\bigr) : S_k-S_{k+1}\le T_k\ (k\le N),\ S_1=s_1,\ S_{N_1+1}=S_B,\ S_{N+1}=s_{N+1},\ S_k\ge0\ (k\in\{2,\dots,N_1\}\cup\{N_1+2,\dots,N\})\Bigr\},
--   $$
--
--   with $\tau_k=S_{k+1}+T_k-S_k$, and let $J$ be the optimal value of the single program in the variables $S_2,\dots,S_N;S_B$ with the same constraints and the extra row $S_B\ge0$. Then the minimum of $V$ over $S_B\ge0$ exists and equals $J$:
--
--   $$
--   \min_{S_B\ge0}V(S_B)=J .
--   $$
--
--   That is, $J=V(S_B)$ for some integer $S_B\ge0$, and $J\le V(S_B)$ for every integer $S_B\ge0$. Optimal values are $+\infty$ for infeasible programs. This is the second of the three equalities that prove (8): the two nested minimizations become one.
--
--   Differences from the source:
--   - reading: Appendix II's displays impose $S_k\ge0$ for $k\in\{1,\dots,N+1\}$ → the §2 index sets $\{2,\dots,N_1\}\cup\{N_1+2,\dots,N\}$; reason: the merged program is the join of $\mathbf P_1$, $\mathbf P_2$ as defined in §2; Appendix II's set would also constrain the fixed values $s_1$, $S_B$, $s_{N+1}$
--   - reading: service times in a discrete-time model → integer $S_k$, $s_1$, $s_{N+1}$, $S_B$; reason: p.5 "We assume a discrete time model", and $D$ of (2) is defined at integer arguments only
--   - generalization: the demand bound $D$ of (2), concave by the assumption on p.6, holding costs $h_k$, mean demand $\mu$, boundary values $s_1$, $s_{N+1}$ → arbitrary $D:\mathbb Z\to\mathbb R$, real $h_k$, $\mu$, integer $s_1$, $s_{N+1}$ without sign conditions; reason: the argument uses no property of these data, and the paper's data are an instance (feasible points have $\tau_k\ge0$, so the values of $D$ at negative arguments are never read)
--   - reading: player 1 controls stages $1,\dots,N_1$ and player 2 stages $N_1+1,\dots,N$ → $1\le N_1<N$; reason: each player controls at least one stage
--   - encoding: optimal values of minimization programs → infima in `EReal`, $\top$ for an infeasible program, decision vectors $\mathbb N\to\mathbb Z$ read at $1,\dots,N+1$; reason: Lean convention; same instances
--   - encoding: $\min_{S_B\ge0}$ → `IsLeast` (a least element, attained at some $S_B\ge0$); reason: this is the meaning of min
-- source:
--   Schoenmeyr, Graves, Coordination of multi-echelon supply chains using the guaranteed service framework, SSRN 3243806, Appendix II, step (B), p.28 (justification p.29)

import Mathlib
import Definitions.Def_GSCoord_Model

namespace GSCoord

/-- Appendix II, step (B) (Schoenmeyr, Graves, Coordination of multi-echelon supply chains using
the guaranteed service framework, SSRN 3243806, Appendix II, step (B), p.28): the minimum over
`S_B ≥ 0` of the optimal value of the merged program with fixed split `S_B` is attained and equals
the optimal value of the single program in the variables `S₂, …, S_N; S_B` with the extra row
`S_B ≥ 0`. "In step (B), we have incorporated the two minimizations into a single program."

**Formalization Note.** "min" is stated as `IsLeast`: the joint optimal value is the value of the
merged program at some `S_B ≥ 0` and is at most its value at every `S_B ≥ 0`. Optimal values are
infima in `EReal`, `⊤` for an infeasible program. Non-negativity follows the §2 index sets.
`1 ≤ N₁ < N`: both players control at least one stage. -/
theorem appendix_II_step_B (sys : SerialSystem) (N₁ : ℕ) (hN₁ : 1 ≤ N₁) (hN₁N : N₁ < sys.N) :
    IsLeast {v : EReal | ∃ SB : ℤ, 0 ≤ SB ∧ v = valFix sys N₁ SB} (valJoint sys N₁) := by sorry

end GSCoord
