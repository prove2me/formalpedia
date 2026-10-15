-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_center_lower_of_auxiliary_probability
-- name    : OAI.FixedClauseThreshold.center_lower_of_auxiliary_probability
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T05:11:58.605411+00:00
-- url     : https://prove2.me/theorems/fd37c8ee-dab0-4753-b4f3-657608fd6b07
-- title:
--   Auxiliary satisfiability above the concentration error forces a lower bound on the $k$-SAT center
-- statement:
--   Fix a clause size $k\ge 3$ and a number of variables $n\ge k+1$.
--
--   For $m\ge 0$ let $Q_k(n,m)$ be the *auxiliary satisfiability probability*: the probability that $m$ independent random auxiliary $k$-clauses on $x_1,\dots,x_n$ have a common satisfying assignment. An auxiliary $k$-clause is an ordered list of $k$ literals drawn independently, each with a uniformly random variable among $x_1,\dots,x_n$ and an independent fair sign (variables may repeat); it is satisfied when at least one of its literals is true.
--
--   Let $\gamma_k(n)$ denote the *normalized center* of the random proper $k$-SAT model on $n$ variables: draw $M=2^{k+1}n$ independent uniformly random proper $k$-clauses $C_1,\dots,C_M$ (each clause uses $k$ distinct variables chosen uniformly among $x_1,\dots,x_n$, with independent fair signs), let the *satisfiable lifetime* $L_n$ be the number of indices $j\in\{1,\dots,M\}$ for which $C_1\wedge\cdots\wedge C_j$ is satisfiable, and set $\gamma_k(n)=\mathbb{E}[L_n]/n$.
--
--   Put $\delta_k=\frac{k-2}{4k}$ and $\varepsilon_k(n)=V_k\,n^{-2\delta_k}$ with $V_k=2\,(2^{k+1})^3\,k\,(2k+2^{k+1}+2)$ (the concentration error).
--
--   **Theorem.** Let $c$ be a real number with $0\le c\le 2^{k+1}$. If
--
--   $$
--   \varepsilon_k(n)<Q_k\bigl(n,\lfloor cn\rfloor\bigr),
--   $$
--
--   then
--
--   $$
--   c-2\,n^{-\delta_k}<\gamma_k(n).
--   $$
--
--   In words: the normalized center cannot lie more than $2n^{-\delta_k}$ below any density $c$ (in the range $[0,2^{k+1}]$) at which the auxiliary model with $\lfloor cn\rfloor$ clauses is still satisfiable with probability exceeding the concentration error. This converts lower bounds on auxiliary satisfiability probabilities, such as those obtained by block interpolation, into lower bounds on centers.
--
--   **Formalization Note** In Lean, $Q_k(n,m)$ is `auxiliaryProbability n k m`, $\varepsilon_k(n)$ is `concentrationError n k`, $n^{-\delta_k}$ is `densityWindow n k`, $\gamma_k(n)$ is `center n k` and $2^{k+1}$ is `capMultiplier k`. The clause count is the natural-number floor `Nat.floor` of $cn$, which is the usual floor because $cn\ge 0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/CenterComparison.lean#L148-L167

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

open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable

theorem OAI.FixedClauseThreshold.center_lower_of_auxiliary_probability {n k : ℕ} (hk : 3 ≤ k) (hn : k + 1 ≤ n)
    {c : ℝ} (hc0 : 0 ≤ c) (hcL : c ≤ capMultiplier k)
    (hprob : concentrationError n k < auxiliaryProbability n k ⌊c * n⌋₊) :
    c - 2 * densityWindow n k < center n k := by sorry
