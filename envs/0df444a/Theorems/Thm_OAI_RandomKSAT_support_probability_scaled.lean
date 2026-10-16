-- Prove2me | Theorems.Thm_OAI_RandomKSAT_support_probability_scaled
-- name    : OAI.RandomKSAT.support_probability_scaled
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T15:20:50.69186+00:00
-- url     : https://prove2.me/theorems/5313fe8d-1804-439c-b6b2-2fac3bad7ca2
-- title:
--   A fixed variable occurs in a uniformly random $k$-clause with probability $k/n$
-- statement:
--   Let $n,k\in\mathbb N$ with $k\le n$. A clause of width $k$ on the variables $[n]=\{0,\dots,n-1\}$ is a pair $c=(V,\beta)$ of a set $V\subseteq[n]$ with $|V|=k$ and a sign map $\beta:V\to\{\mathrm T,\mathrm F\}$; let $\mathcal C_{n,k}$ be the finite set of such clauses. For a variable $v\in[n]$ let
--   $$
--   p_v=\frac{1}{|\mathcal C_{n,k}|}\sum_{c=(V,\beta)\in\mathcal C_{n,k}}\mathbf 1\{v\in V\}
--   $$
--   be the probability that $v$ occurs in a uniformly random clause of width $k$.
--
--   **Theorem.** For every variable $v\in[n]$,
--   $$
--   n\cdot p_v=k .
--   $$
--
--   Since a variable exists only when $n\ge1$, this says $p_v=k/n$. It is the basic input for overlap estimates: two independent uniform clauses both contain a given variable with probability $(k/n)^2$, so the expected number of variables they share is $k^2/n$.
--
--   **Formalization Note** $p_v$ is `favg` of the $0/1$ indicator that $v$ lies in the variable set of the clause, taken over the type `Clause n k`. The hypothesis $k\le n$ makes this type nonempty.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/SupportProbabilities.lean#L40-L52

import Mathlib
import Definitions.Def_SATSharpness
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration
import Definitions.Def_OAI_Probability_SATVariance_SupportProbabilities

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.support_probability_scaled {n k : ℕ} (hkn : k ≤ n) (v : Fin n) :
    (n : ℝ)*favg (fun c : Clause n k => if v ∈ c.1.1 then (1 : ℝ) else 0) = k := by sorry
