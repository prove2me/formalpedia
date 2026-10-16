-- Prove2me | Theorems.Thm_OAI_RandomKSAT_killRatio_limit
-- name    : OAI.RandomKSAT.killRatio_limit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T15:25:14.582973+00:00
-- url     : https://prove2.me/theorems/9fc82fe4-bd84-40d9-8e9c-1e6fa70bf0c7
-- title:
--   Asymptotics $N^s\kappa(N^{m+1},N^m,s)\to2^{-s}$ of the kill ratio
-- statement:
--   For natural numbers $u,b,s$ let $\kappa(u,b,s)=\binom bs/(2^s\binom us)$ be the kill ratio. When a nonempty set of assignments of $u$ Boolean variables has exactly $b$ frozen variables (variables on which all its members agree), $\kappa(u,b,s)$ is the probability that a uniformly random clause of width $s$ (an $s$-element set of variables with a sign for each, satisfied by an assignment that matches at least one sign) is violated by every member of the set.
--
--   **Theorem.** Let $m\ge1$ and $s\ge0$ be integers. Then
--   $$
--   \lim_{N\to\infty}N^s\,\kappa\big(N^{m+1},N^m,s\big)=\frac{1}{2^s},
--   $$
--   where $N$ runs through the natural numbers.
--
--   With $u=N^{m+1}$ variables of which the fraction $b/u=1/N$ is frozen, each of the $s$ variables of a random clause is frozen with probability about $1/N$ and receives the opposing sign with probability $1/2$, so $\kappa\approx(2N)^{-s}$. The limit supplies the precise one-clause kill probabilities of subcubes in the asymptotic estimates for block killing and lifetimes.
--
--   **Formalization Note** The parameters $N^{m+1}$ and $N^m$ are natural-number powers, and the limit is taken along the filter `atTop` on $\mathbb N$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/SharpnessEstimates.lean#L58-L74

import Mathlib
import Definitions.Def_SATSharpness
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration
import Definitions.Def_OAI_Probability_SATVariance_SupportProbabilities
import Definitions.Def_OAI_Probability_SATVariance_Subcube

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal Topology

theorem OAI.RandomKSAT.killRatio_limit {m : ℕ} (hm : 0 < m) (s : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ)^s * killRatio (N^(m+1)) (N^m) s)
      atTop (𝓝 (((2 : ℝ)^s)⁻¹)) := by sorry
