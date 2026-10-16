-- Prove2me | Theorems.Thm_OAI_RandomKSAT_favg_shuffle
-- name    : OAI.RandomKSAT.favg_shuffle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T18:22:19.971822+00:00
-- url     : https://prove2.me/theorems/1ef8cd2c-bbf7-432d-b787-89d90abfd232
-- title:
--   Words of independent uniform letters are exchangeable: shuffling preserves averages
-- statement:
--   Let $\alpha$ be a finite nonempty set and $m\in\mathbb N$. For a finite sequence $u=(u_1,\dots,u_m)$ over $\alpha$ and a function $f$ from finite sequences over $\alpha$ to $\mathbb R$, define the *shuffle average*
--   $$
--   \operatorname{Sh}_u(f)=\frac1{m!}\sum_{\sigma\in S_m}f\big(u_{\sigma(1)},\dots,u_{\sigma(m)}\big),
--   $$
--   where $S_m$ is the group of permutations of $\{1,\dots,m\}$; it is the average of $f$ over all $m!$ rearrangements of $u$, counted with multiplicity when $u$ has repeated entries. For $h:\alpha^m\to\mathbb R$ write $\mathbb E_{w\in\alpha^m}[h(w)]=|\alpha|^{-m}\sum_{w\in\alpha^m}h(w)$ for the uniform average.
--
--   **Theorem.** For every function $f$ on finite sequences over $\alpha$,
--   $$
--   \mathbb E_{w\in\alpha^m}\big[\operatorname{Sh}_w(f)\big]=\mathbb E_{w\in\alpha^m}\big[f(w_1,\dots,w_m)\big].
--   $$
--
--   In probabilistic language, a word of $m$ independent uniform letters is exchangeable: permuting it by an independent uniformly random permutation does not change its distribution. This allows one to rearrange a word of independent uniform random clauses, for instance to move selected clauses to random positions, without changing the expectation of any statistic of the word.
--
--   **Formalization Note** The shuffle average is `shuffleAvg (List.ofFn w) f`, the average of `f` over Mathlib's list `List.permutations'`, which enumerates the $m!$ rearrangements with multiplicity; uniform averages over the finite type `Fin m → α` are `favg`. The function `f` is defined on all lists over $\alpha$, of any length.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/ShuffleAverages.lean#L180-L218

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
import Definitions.Def_OAI_Probability_SATVariance_CapBridge
import Definitions.Def_OAI_Probability_SATVariance_ShuffleAverages

open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem OAI.RandomKSAT.favg_shuffle.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (m : ℕ) (f : List α → ℝ) :
    favg (fun w : Fin m → α => shuffleAvg (List.ofFn w) f) =
      favg (fun w : Fin m → α => f (List.ofFn w)) := by sorry
