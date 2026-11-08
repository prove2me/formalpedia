-- Prove2me | Theorems.Thm_LearnVsOpt_vertexSel_valid
-- name    : LearnVsOpt.vertexSel_valid
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:04:55.201198+00:00
-- url     : https://prove2.me/theorems/867a338c-29fd-48bd-a1b5-282273f3a2db
-- title:
--   §2, p.6; (9), p.12 — a valid response exists, computed by vertex enumeration in polynomial time
-- statement:
--   Let $j_0$ be the null action and $\rho_L\in(0,1]$. For every $(u,c)\in[0,1]^{2n_L}$ with $c[j_0]=0$, the learner's two-constraint linear program has a best response of support at most two, and its dual (9) has a minimizer $\lambda\in[0,1/\rho_L]$. The concrete selector `vertexSel` returns a valid such response, in at most $a\,n_L^d$ unit operations, with $a$ and $d$ absolute.
--
--   This shows the clauses that hold for all valid selectors are not vacuous, and it supplies the linear-programming step of the running-time clause.
--
--   Differences from the source:
--   - reading: "there is always a best response y … with support at most two" (p.6); "we can always pick λ(f) ∈ [0, 1/ρ_L]" (p.12); "solves a linear program in n_L variables" (p.22) → vertexSel is a valid selector, with charge at most a·n_L^d on all real (u, c); reason: the three unnumbered statements, made concrete in one selector so the running-time clause has no oracle
--   - encoding: "the null action has cost 0 and utility at least 0" → c[j₀] = 0 with u ∈ [0, 1]^{n_L}; reason: same content
-- source:
--   Fikioris, Sivan & Tardos, Learning vs. Optimizing Players in Budgeted Games, arXiv:2611.05580, §2, p.6; (9), p.12; proof of Theorem 6.7, p.22

import Mathlib
import Definitions.Def_LearnVsOpt_Selection

namespace LearnVsOpt

/-- **A valid selector exists, at polynomial cost** (Fikioris, Sivan & Tardos, arXiv:2611.05580, §2,
p.6; (9), p.12; p.22). The learner's LP has a best response of support at most two, its dual has a
minimizer `λ ∈ [0, 1/ρ_L]`, and the charged vertex enumeration `vertexSel` finds both on every
`(u, c) ∈ [0, 1]^{2n_L}` with `c[j₀] = 0`, in `O(n_L^d)` unit operations, uniformly in the data. -/
theorem vertexSel_valid :
    ∃ a d : ℕ, ∀ {nL : ℕ} (j₀ : Fin nL) (ρL : ℝ), 0 < ρL → ρL ≤ 1 →
      IsValidSel j₀ ρL (vertexSel j₀ ρL) ∧
      ∀ u c : Fin nL → ℝ, (vertexSel j₀ ρL u c).cost ≤ a * nL ^ d := by sorry

end LearnVsOpt
