-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_summable_min_convergence
-- name    : OAI.FixedClauseThreshold.summable_min_convergence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T05:17:22.148091+00:00
-- url     : https://prove2.me/theorems/cb236855-8609-4349-a255-4940d8370d02
-- title:
--   Convergence of bounded sequences with polynomially small min-superadditivity defects
-- statement:
--   Let $u:\mathbb{N}\to\mathbb{R}$ be a sequence that is eventually bounded above and eventually bounded below, and let $A\ge0$ and $\beta>0$ be real numbers. Suppose there is $N\in\mathbb{N}$ such that
--
--   1. for all $r,s\ge N$: $\ \min(u_r,u_s)-A\,\min(r,s)^{-\beta}\le u_{r+s}$;
--   2. for all $s\ge N$: $\ u_s-A\,s^{-\beta}\le u_{s+1}$.
--
--   Then $u$ converges, and its limit is its limit superior:
--
--   $$
--   \lim_{n\to\infty}u_n=\limsup_{n\to\infty}u_n .
--   $$
--
--   This is a Fekete-type convergence lemma that does not require subadditivity: two-sided boundedness together with approximate min-superadditivity and approximate one-step monotonicity, with errors decaying like a negative power of the index, already force convergence. It is applied to the normalized centers of random $k$-SAT, whose limit becomes the satisfiability threshold.
--
--   **Formalization Note** Boundedness is stated with `Filter.IsBoundedUnder` along `Filter.atTop` for the orders $\le$ (bounded above) and $\ge$ (bounded below), and the limit is `Filter.limsup u Filter.atTop`, which for such a sequence is the usual limit superior. The power $x^{-\beta}$ is Lean's real power, with $0^{-\beta}=0$; this only matters in the hypotheses when $N=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/Convergence.lean#L141-L173

import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement
import Definitions.Def_OAI_Probability_RandomSAT_FiniteMean
import Definitions.Def_OAI_Probability_RandomSAT_ClauseProcess
import Definitions.Def_OAI_Probability_RandomSAT_Binomial
import Definitions.Def_OAI_Probability_RandomSAT_Forcing
import Definitions.Def_OAI_Probability_RandomSAT_Variance
import Definitions.Def_OAI_Probability_RandomSAT_Concentration
import Definitions.Def_OAI_Probability_RandomSAT_CenterBounds
import Definitions.Def_OAI_Probability_RandomSAT_Interpolation
import Definitions.Def_OAI_Probability_RandomSAT_Transfer
import Definitions.Def_OAI_Probability_RandomSAT_CenterComparison
import Definitions.Def_OAI_Probability_RandomSAT_Convergence

open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable

theorem OAI.FixedClauseThreshold.summable_min_convergence (u : ℕ → ℝ) {A β : ℝ} (hA : 0 ≤ A) (hβ : 0 < β)
    (hUpper : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop u)
    (hLower : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop u)
    (hcompare : ∃ N : ℕ,
      (∀ r ≥ N, ∀ s ≥ N, min (u r) (u s) - A * (min r s : ℝ)^(-β) ≤ u (r + s)) ∧
      (∀ s ≥ N, u s - A * (s : ℝ)^(-β) ≤ u (s + 1))) :
    Filter.Tendsto u Filter.atTop (nhds (Filter.limsup u Filter.atTop)) := by sorry
