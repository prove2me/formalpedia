-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_balanced_blocks_bound
-- name    : OAI.FixedClauseThreshold.balanced_blocks_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T05:15:40.243157+00:00
-- url     : https://prove2.me/theorems/29053710-1d02-483f-852e-9b65e91627f4
-- title:
--   Balanced block bound for approximately min-superadditive sequences
-- statement:
--   Let $u:\mathbb{N}\to\mathbb{R}$ be a sequence, let $A\ge 0$ and $\beta>0$ be real numbers, and let $N,s$ be natural numbers with $N\le s$ and $s\ge 1$. Put
--
--   $$
--   B_\beta=\frac{3^\beta}{(3/2)^\beta-1}>0 .
--   $$
--
--   Assume
--
--   1. for all natural numbers $r,t\ge N$: $\ \min(u_r,u_t)-A\,\min(r,t)^{-\beta}\le u_{r+t}$;
--   2. $u_s-A\,s^{-\beta}\le u_{s+1}$.
--
--   Then for every natural number $q\ge 1$ and every natural number $r$ with $0\le r\le q$,
--
--   $$
--   u_s-A\,s^{-\beta}-A\,B_\beta\,s^{-\beta}\bigl(1-q^{-\beta}\bigr)\le u_{qs+r}.
--   $$
--
--   Thus a single index $s$ controls the sequence from below on all indices $qs+r$ with $r\le q$, with a loss of order $s^{-\beta}$ that is uniform in $q$. Since every $n\ge s^2$ can be written as $qs+r$ with $q=\lfloor n/s\rfloor\ge s$ and $r=n\bmod s<s\le q$, this yields a uniform lower bound on the whole tail $n\ge s^2$, which is the key step in a Fekete-type convergence argument that needs only min-comparisons with polynomially decaying errors.
--
--   **Formalization Note** The power $x^{-\beta}$ is Lean's real power `Real.rpow`, for which $0^{-\beta}=0$; this convention only affects hypothesis 1 when $N=0$ and $\min(r,t)=0$. The constant $B_\beta$ is `balanceConstant β`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/Convergence.lean#L41-L121

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

theorem OAI.FixedClauseThreshold.balanced_blocks_bound (u : ℕ → ℝ) {A β : ℝ} (hA : 0 ≤ A) (hβ : 0 < β)
    {N s : ℕ} (hsN : N ≤ s) (hs : 0 < s)
    (hadd : ∀ r ≥ N, ∀ t ≥ N,
      min (u r) (u t) - A * (min r t : ℝ)^(-β) ≤ u (r + t))
    (hnext : u s - A * (s : ℝ)^(-β) ≤ u (s + 1)) :
    ∀ q : ℕ, 1 ≤ q → ∀ r : ℕ, r ≤ q →
      u s - A * (s : ℝ)^(-β) -
        A * balanceConstant β * (s : ℝ)^(-β) * (1 - (q : ℝ)^(-β)) ≤ u (q * s + r) := by sorry
