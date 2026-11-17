-- Prove2me | Theorems.Thm_MultitaskContracts_Supplement_theorem_6
-- name    : MultitaskContracts.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:09:08.40699+00:00
-- url     : https://prove2.me/theorems/936a4765-3cb5-4ea8-9086-d952e470742b
-- title:
--   Theorem 6 — for independent tasks the explicit clipped contract $\hat t$ implements full effort with budget $\le10\,\mathrm{OPT}^{\mathrm{Bun}}_{\mathrm{MinBudget}}$
-- statement:
--   Let $I$ be an instance of the multitask model with independent tasks. There is a contract that implements full effort with budget at most $10\,\mathrm{OPT}^{\mathrm{Bun}}_{\mathrm{MinBudget}}$, and it can be computed and evaluated efficiently. Namely, the clipped contract of eq. (23),
--   $$\hat t(Y)=\frac54\min\Bigl\{8L,\ \max\Bigl\{0,\ t_{\mathrm{Sep}}(Y)-\mu+\tfrac{11}{2}L\Bigr\}\Bigr\},$$
--   with $\mu$, $\sigma$, $L$ as in its definition, satisfies:
--   1. $\hat t(Y)\ge0$ for every performance $Y$ (it is a bundle contract);
--   2. $\hat t$ implements full effort, i.e. $K$ is a best response of the agent to $\hat t$;
--   3. $\hat t(Y)\le10\,\mathrm{OPT}^{\mathrm{Bun}}_{\mathrm{MinBudget}}$ for every performance $Y$.
--
--   Theorem 5 shows that the exact Min-Budget optimum is NP-hard to compute; this theorem gives a constant-factor approximation in one pass over the tasks.
--
--   **Formalization Note** The budget bound is stated in $[0,\infty]$ as $\hat t(Y)\le10\,\mathrm{OPT}^{\mathrm{Bun}}_{\mathrm{MinBudget}}$ for every $Y$, with the published optimum over bundle contracts. "Computed and evaluated efficiently" is encoded by the explicit closed form: $\mu$, $\sigma$, $L$ and $t_{\mathrm{Sep}}(Y)$ are single sums over the tasks.
--
--   Differences from the source:
--   - encoding: there exists a contract … and it can be computed and evaluated efficiently → the explicit contract clippedContract I of eq. (23) (closed form from single sums over the tasks) has the three properties; reason: the explicit witness of the paper's proof implies the existence claim, and its closed form is what the proof's "Running time" paragraph calls efficient
--   - encoding: budget at most 10·OPT^Bun_MinBudget → ∀ Y, ENNReal.ofReal (ˆt Y) ≤ 10 * I.optMinBudget (bundle K); reason: the budget is max_Y ˆt(Y); optima live in ℝ≥0∞
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), Theorem 6, p.36 (PDF p.38); the contract is eq. (23), p.37 (PDF p.39)

import Mathlib
import Definitions.Def_MultitaskContracts_Instance
import Definitions.Def_MultitaskContracts_bundle
import Definitions.Def_MultitaskContracts_Instance_IsIndependent
import Definitions.Def_MultitaskContracts_Supplement_clippedContract

set_option autoImplicit false

open scoped ENNReal

namespace MultitaskContracts.Supplement

/-- **Theorem 6** (§5.2, p.36, PDF 38). For independent tasks, there exists a contract that
implements full effort with budget at most `10·OPT^Bun_MinBudget`, and it can be computed and
evaluated efficiently: the explicit contract `ˆt` of Eq. (23) is a bundle contract (nonnegative),
implements full effort, and pays at most `10·OPT^Bun_MinBudget` on every performance.
E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), Theorem 6, p.36, and eq. (23), p.37.

**Formalization Note.** The witness is `clippedContract I`, the closed form (23) built from
single sums over the tasks (`µ`, `σ`, `L`, `t_Sep`); this is how "computed and evaluated
efficiently" is encoded. The budget bound is `ofReal (ˆt(Y)) ≤ 10·OPT^Bun_MinBudget` for every
`Y` in `ℝ≥0∞` (published `Instance.optMinBudget` over `bundle K`). -/
theorem theorem_6 {K : Type*} [Fintype K] [DecidableEq K] (I : Instance K)
    (hI : I.IsIndependent) :
    clippedContract I ∈ bundle K ∧ I.Implements (clippedContract I) Finset.univ ∧
      ∀ Y : Finset K, ENNReal.ofReal (clippedContract I Y) ≤ 10 * I.optMinBudget (bundle K) := by sorry

end MultitaskContracts.Supplement
