-- Prove2me | Theorems.Thm_KMedian195_originalPrimalUpperBound_exact
-- name    : KMedian195.originalPrimalUpperBound_exact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T17:49:50.265241+00:00
-- url     : https://prove2.me/theorems/a0e68ae9-c8d9-41cd-9f88-2c11440971c3
-- title:
--   Theorem 4.4 (Part I) — the factor-revealing program has value at most $2-(\gamma-1)^2$ for $\gamma\in[1,1.224]$
-- statement:
--   This is Theorem 4.4 of Part I (arXiv:2610.18144): for every $\gamma\in[1,1.224]$, the factor-revealing program of Definition 4.1 with the bid $\beta_\gamma(\alpha,d)=[\alpha-\gamma d]^+$ has value at most $2-(\gamma-1)^2$, in every dimension $n\ge1$.
--
--   **The program.** Let $\beta_\gamma(\alpha,d)=\max(\alpha-\gamma d,0)$. For $n\ge1$, the variables are real numbers $f$, $d_j$ ($1\le j\le n$) and $r_{j,\ell}$ ($1\le j\le n$, $1\le\ell\le n+1$). The objective is
--
--   $$\sum_{j=1}^{n}\Big(\sum_{i=j}^{n}\beta_\gamma\big(r_{j,i},\,r_{j,i+1}\big)+r_{j,n+1}\Big)-f .$$
--
--   A solution is *feasible* if:
--
--   1. $\sum_{j=1}^n d_j=1$;
--   2. $r_{j,i+1}\le r_{j,i}$ for all $j\le i\le n$;
--   3. $r_{k,k}\le r_{j,k}+d_k+d_j$ for all $j<k$;
--   4. $r_{j,\ell}\le r_{k,\ell}+d_k+d_j$ for all $j\ne k$ and all $\ell>\max(j,k)$;
--   5. $\sum_{j<k}\beta_\gamma(r_{j,k},d_j)+\sum_{j\ge k}\beta_\gamma(r_{k,k},d_j)\le f$ for every $k$;
--   6. $f\ge0$, $d_j\ge0$ for all $j$, and $r_{j,\ell}\ge0$ for all $j$ and $\ell$.
--
--   **Statement.** Let $\gamma$ be a real number with $1\le\gamma\le\frac{153}{125}=1.224$. Then for every $n\ge1$, every feasible solution $(d,f,r)$ of the program satisfies
--
--   $$\sum_{j=1}^{n}\Big(\sum_{i=j}^{n}\beta_\gamma\big(r_{j,i},\,r_{j,i+1}\big)+r_{j,n+1}\Big)-f\ \le\ 2-(\gamma-1)^2 .$$
--
--   **Role.** The analysis of the greedy algorithm maps a run of the algorithm to a feasible solution of this program, so the bound gives the robust LMP guarantee (Part I, Theorem D.7) with the factor $\rho=2-(1.224-1)^2=1.949824$ at $\gamma=1.224$. This is the source of the constant $1.9499$ in the pseudo-approximation (Theorem 1.2) and in the facility-location theorem (Theorem 1.4), and hence of $1.95$ in Theorem 1.1.
--
--   **Formalization Note** Indices are shifted by one in the code (clients $0,\dots,n-1$, times $0,\dots,n$). The paper's variable $r_{j,\ell}$ exists only for $\ell\ge j$; here $r_{j,\ell}$ is defined for all $\ell$, and the entries with $\ell<j$ occur only in the nonnegativity constraint.
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (Part I: arXiv:2610.18144, https://arxiv.org/abs/2610.18144; Part II: arXiv:2610.17172, https://arxiv.org/abs/2610.17172); Part I (arXiv:2610.18144), Theorem 4.4. Lean source: `KMedian195.originalPrimalUpperBound_exact`, https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/Imported/KMedian195/Main.lean#L29-L36

/-
Copied from `epfl-thl2/project-k-median` (written by Codex),
commit `d87e2a20376896ab72fe005a493b3af970a0f82d`, the last three theorems of
`bound-195/KMedian195/FactorRevealingPrimal.lean`. The first and last are the two theorems of
`bound-195/Challenge.lean`, which the source checks with the comparator.
Changes: module header (`module`, `public import`, `@[expose] public section`) and a module
docstring; the theorems are moved here from `Imported/KMedian195/FactorRevealingPrimal.lean`.
-/
module

public import Definitions.Def_KMedian195_FactorRevealingPrimal

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

@[expose] public section

namespace KMedian195

noncomputable section

theorem originalPrimalUpperBound_exact
    (gamma : ℝ) (hγlo : 1 ≤ gamma) (hγhi : gamma ≤ (153 : ℝ) / 125) :
    OriginalPrimalUpperBound gamma (2 - (gamma - 1) ^ 2) := by sorry

end
end KMedian195
end
