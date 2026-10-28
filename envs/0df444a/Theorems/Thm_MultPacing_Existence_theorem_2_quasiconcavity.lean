-- Prove2me | Theorems.Thm_MultPacing_Existence_theorem_2_quasiconcavity
-- name    : MultPacing.Existence.theorem_2_quasiconcavity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:30:11.170303+00:00
-- url     : https://prove2.me/theorems/7c48c051-09cc-4b82-87be-dea33df7d591
-- title:
--   Proof of Theorem 2, "Quasiconcavity of utility in the buyer's own strategy", p. 12 — spend increasing; utility increasing below budget, decreasing above when H > M/ϵ
-- statement:
--   Fix a pacing game, $\epsilon>0$, $H$, a buyer $i$ and the multipliers $\alpha_{-i}\in[0,1]^{N\setminus\{i\}}$ of the other buyers. For $a\in[0,1]$ write $\sigma(a)=a\epsilon+\sum_j s_{ij}$ for buyer $i$'s total spend and $u(a)$ for her utility in the $(\epsilon,H)$-smoothed pacing game when she plays $\alpha_i=a$. Then:
--
--   1. $\sigma$ is continuous and strictly increasing on $[0,1]$;
--   2. $u$ is strictly increasing on $\{a\in[0,1]:\sigma(a)\le B_i\}$;
--   3. if $M$ satisfies $\sum_j v_{kj}+2\epsilon\le M$ for every buyer $k$ and $H>M/\epsilon$, then $u$ is strictly decreasing on $\{a\in[0,1]:\sigma(a)\ge B_i\}$.
--
--   Since $\sigma$ is increasing, the two sets are $[0,t]$ and $[t,1]$ for the point $t$ where the spend reaches $B_i$ (or $t=1$ if it never does), so $u$ increases up to $t$ and decreases after it:
--   $$
--   u \text{ is strictly increasing on } \{\sigma\le B_i\}\ \text{ and strictly decreasing on } \{\sigma\ge B_i\}.
--   $$
--   In particular $u$ is quasiconcave in the buyer's own strategy, which is the second hypothesis of the existence theorem behind Theorem 2; part 2 is also used in the proof of Theorem 1.
--
--   **Formalization Note** The other buyers' multipliers enter through a profile $\alpha$ with all entries in $[0,1]$, and buyer $i$'s entry is replaced by $a$ (`Function.update α i a`).
--
--   Differences from the source:
--   - generalization: the bullet is argued under Theorem 2's hypotheses ($H>M/\epsilon$, and Definition 3's $H>0$) → parts 1 and 2 for every real $H$, part 3 under $\sum_j v_{kj}+2\epsilon\le M$ and $H>M/\epsilon$; reason: below the budget the utility does not involve $H$, and the spend never does, so the bound on $H$ is needed only for part 3; with the hypotheses in place the statement is the source's.
--   - reading: "$u_i$ is increasing", "total spend … is increasing", "utility is decreasing" → strictly increasing / strictly decreasing; reason: the paper itself recalls the claim as "strictly increasing … (the strictness is due to the artificial good)" in the proof of Theorem 1, and the strict reading is the stronger one.
--   - encoding: "there exists a number $t$ such that for $\alpha_i<t$, $u_i$ is nondecreasing … for $\alpha_i>t$ nonincreasing", with $t$ the solution of $\alpha_i\epsilon+\sum_j s_{ij}=B_i$ or $t=1$ → monotonicity on the sets $\{\sigma\le B_i\}$ and $\{\sigma\ge B_i\}$; reason: since $\sigma$ is continuous and strictly increasing (part 1) these sets are exactly $[0,t]$ and $[t,1]$ (the second empty when $t=1$ is not attained).
-- source:
--   Conitzer, Kroer, Sodomka & Stier-Moses, Multiplicative Pacing Equilibria in Auction Markets, arXiv:1706.07151v5, p. 12 (PDF 12), proof of Theorem 2, bullet "Quasiconcavity of utility in the buyer's own strategy"

import Mathlib
import Definitions.Def_MultPacing_Existence_Smoothed

namespace MultPacing.Existence

theorem theorem_2_quasiconcavity {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G]
    (P : PacingGame N G) (ε H M : ℝ) (hε : 0 < ε) (α : N → ℝ)
    (hα : ∀ k, α k ∈ Set.Icc (0 : ℝ) 1) (i : N) :
    (ContinuousOn (fun a => smSpend P ε (Function.update α i a) i) (Set.Icc 0 1) ∧
      StrictMonoOn (fun a => smSpend P ε (Function.update α i a) i) (Set.Icc 0 1)) ∧
    StrictMonoOn (fun a => smUtility P ε H (Function.update α i a) i)
      {a | a ∈ Set.Icc (0 : ℝ) 1 ∧ smSpend P ε (Function.update α i a) i ≤ P.B i} ∧
    ((∀ k, ∑ j, P.v k j + 2 * ε ≤ M) → M / ε < H →
      StrictAntiOn (fun a => smUtility P ε H (Function.update α i a) i)
        {a | a ∈ Set.Icc (0 : ℝ) 1 ∧ P.B i ≤ smSpend P ε (Function.update α i a) i}) := by sorry

end MultPacing.Existence
