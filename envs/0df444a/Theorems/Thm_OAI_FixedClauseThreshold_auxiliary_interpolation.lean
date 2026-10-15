-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_auxiliary_interpolation
-- name    : OAI.FixedClauseThreshold.auxiliary_interpolation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T05:05:45.513695+00:00
-- url     : https://prove2.me/theorems/0ab3a1df-14fe-4e89-90e8-65e0edca0e24
-- title:
--   Partition interpolation inequality for the auxiliary random $k$-SAT model
-- statement:
--   For $N\ge1$ and $k\in\mathbb N$, an *auxiliary $k$-clause* on the Boolean variables $x_1,\dots,x_N$ is an ordered $k$-tuple of independent uniformly random literals $(x_i,b)$ with $i\in\{1,\dots,N\}$ and $b\in\{0,1\}$ (variables may repeat); an assignment satisfies it if it agrees with at least one of its literals. Let $Q_N(m)$ be the probability that $m$ independent auxiliary $k$-clauses on $N$ variables are simultaneously satisfiable. Then for all integers $r,s\ge1$ and $m\ge0$, with $p=r/(r+s)$,
--
--   $$
--   \sum_{j=0}^{m}\binom mj p^{j}(1-p)^{m-j}\,Q_r(j)\,Q_s(m-j)\ \le\ Q_{r+s}(m),
--   $$
--
--   that is, $\mathbb E_{J\sim\operatorname{Bin}(m,p)}\big[Q_r(J)\,Q_s(m-J)\big]\le Q_{r+s}(m)$.
--
--   The left side is the satisfiability probability of a partitioned model: the $r+s$ variables are split into blocks of sizes $r$ and $s$, and each clause independently lives entirely in the first block (with probability $p$) or entirely in the second, with uniform literals there; such a formula is satisfiable if and only if both of its parts are. The inequality states that confining the clauses to blocks can only decrease the probability of satisfiability. It is a fixed-clause-count form of partition interpolation, and it is used to compare the auxiliary model on $r+s$ variables with the models on its two blocks.
--
--   **Formalization Note** $Q_N(m)$ is `auxiliaryProbability N k m`, the $m$-fold iterate of `auxiliaryAverage k` applied to `alive` and evaluated at the full cube, with clauses of type `Fin k → Fin N × Bool`. The binomial expectation is `binomialMean (r / (r + s)) m`, defined by its first-trial recursion.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/Interpolation.lean#L397-L420

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

open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable

theorem OAI.FixedClauseThreshold.auxiliary_interpolation {r s k : ℕ} (hr : 0 < r) (hs : 0 < s) (m : ℕ) :
    binomialMean ((r : ℝ) / (r + s)) m (fun j =>
      auxiliaryProbability r k j * auxiliaryProbability s k (m - j)) ≤
      auxiliaryProbability (r + s) k m := by sorry
