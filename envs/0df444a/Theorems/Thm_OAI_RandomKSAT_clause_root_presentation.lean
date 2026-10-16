-- Prove2me | Theorems.Thm_OAI_RandomKSAT_clause_root_presentation
-- name    : OAI.RandomKSAT.clause_root_presentation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:18:18.976186+00:00
-- url     : https://prove2.me/theorems/f0856c5b-5ab5-4b6a-b1bc-5a124e8ebe1c
-- title:
--   Every clause is the root clause of a suitable splitting of the variables
-- statement:
--   Write $[m]=\{0,\dots,m-1\}$ and $\{0,1\}$ for the Booleans. A *$k$-clause on $[n]$* is a pair $c=(V,\sigma)$ with $V\subseteq[n]$, $|V|=k$, and signs $\sigma:V\to\{0,1\}$; an assignment $y\in\{0,1\}^n$ *satisfies* $c$ if $y_v=\sigma_v$ for some $v\in V$. Given a bijection $e:[k]\sqcup[n-k]\to[n]$ and $(x,b)\in\{0,1\}^k\times\{0,1\}^{n-k}$, the *joined assignment* $e(x,b)\in\{0,1\}^n$ takes the value $x_j$ at $e(\mathrm{inl}\,j)$ and $b_v$ at $e(\mathrm{inr}\,v)$.
--
--   **Theorem.** For every $k$-clause $c$ on $[n]$ there exist a bijection $e:[k]\sqcup[n-k]\to[n]$ and an assignment $a\in\{0,1\}^k$ such that for all $(x,b)\in\{0,1\}^k\times\{0,1\}^{n-k}$,
--
--   $$
--   c\ \text{is not satisfied by}\ e(x,b)\iff x=a .
--   $$
--
--   In other words, after relabelling the variables so that the variables of $c$ become the $k$ root variables, $c$ is falsified exactly when the root part of the assignment equals one specific pattern $a$ (the negation of the signs of $c$), independently of the remaining $n-k$ variables. This puts an arbitrary clause in the normal form required by the deletion estimate, in which the deleted clause is the root clause of a root/outer splitting.
--
--   **Formalization Note** Here $n-k$ is natural-number subtraction; when $k>n$ there are no $k$-clauses on $[n]$ and the statement is vacuous. The bijection is an equivalence `Fin k ⊕ Fin (n-k) ≃ Fin n` and the joined assignment is `joinedAssignment e x`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/OmissionCompression.lean#L159-L187

import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiniteVariance
import Definitions.Def_OAI_Probability_SATVariance_LifetimePotential
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiberRefresh
import Definitions.Def_OAI_Probability_SATVariance_PairEvolution
import Definitions.Def_OAI_Probability_SATVariance_HiddenTests
import Definitions.Def_OAI_Probability_SATVariance_WeightedRewards
import Definitions.Def_OAI_Probability_SATVariance_CountMoments
import Definitions.Def_OAI_Probability_SATVariance_SupportProbabilities__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_OmissionCompression

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.clause_root_presentation {n k : ℕ} (c : Clause n k) :
    ∃ (e : Fin k ⊕ Fin (n-k) ≃ Fin n) (a : Assignment k),
      ∀ x, ¬Satisfies c (joinedAssignment e x) ↔ x.1 = a := by sorry
