-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_concentration_capped
-- name    : OAI.FixedClauseThreshold.concentration_capped
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:57:07.682526+00:00
-- url     : https://prove2.me/theorems/0376842d-e77b-4433-9373-aa51f010ee8d
-- title:
--   Polynomial concentration of the capped satisfiability lifetime of random $k$-SAT
-- statement:
--   Let $k\ge3$ and $n\ge k+1$. A *proper $k$-clause* on the Boolean variables $x_1,\dots,x_n$ is a choice of $k$ distinct variables with a sign (a required truth value) for each; an assignment satisfies it if it agrees with at least one of the signs. Put $L_k=2^{k+1}$ and $M=L_k\,n$, and let $F=(C_1,\dots,C_M)$ be a sequence of $M$ independent uniformly random proper $k$-clauses. Its *capped lifetime*
--
--   $$
--   \Lambda(F)=\#\big\{j\in\{1,\dots,M\}:\ C_1,\dots,C_j\text{ are simultaneously satisfiable}\big\}
--   $$
--
--   counts the satisfiable initial segments, and its normalized center is $c_{n,k}=\mathbb E[\Lambda]/n$. Let
--
--   $$
--   \delta_k=\frac{k-2}{4k},\qquad \eta_k=\frac{k-2}{2k},\qquad V_k=2L_k^3\,k\,(2k+L_k+2).
--   $$
--
--   Then
--
--   $$
--   \Pr\Big[\,\big|\Lambda(F)-n\,c_{n,k}\big|\ \ge\ n^{1-\delta_k}\Big]\ \le\ V_k\,n^{-\eta_k}.
--   $$
--
--   Since satisfiability of initial segments is monotone, for $m\le M$ the event $\Lambda(F)\ge m$ is exactly the event that the first $m$ clauses are satisfiable. The theorem therefore says that the number of clauses a random $k$-SAT formula on $n$ variables absorbs before becoming unsatisfiable deviates from $n\,c_{n,k}$ by at least $n^{1-\delta_k}=o(n)$ only with polynomially small probability. Consequently the satisfiability probability with $m$ clauses is at least $1-V_kn^{-\eta_k}$ for $m\le nc_{n,k}-n^{1-\delta_k}$ and at most $V_kn^{-\eta_k}$ for $nc_{n,k}+n^{1-\delta_k}<m\le M$.
--
--   **Formalization Note** $M$ is `mainCap n k` $=$ `capMultiplier k * n`, $\Lambda$ is `lifetime k (mainCap n k) Finset.univ`, $c_{n,k}$ is `center n k`, $n^{1-\delta_k}$ is `fluctuationWindow n k` (a real power) and $V_kn^{-\eta_k}$ is `concentrationError n k` with $V_k$ = `varianceConstant k`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/Concentration.lean#L214-L237

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

open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable

theorem OAI.FixedClauseThreshold.concentration_capped {n k : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n) :
    uniformProbability (fun F : Formula n k (mainCap n k) =>
      fluctuationWindow n k ≤ |lifetime k (mainCap n k) Finset.univ F -
        (n : ℝ) * center n k|) ≤ concentrationError n k := by sorry
