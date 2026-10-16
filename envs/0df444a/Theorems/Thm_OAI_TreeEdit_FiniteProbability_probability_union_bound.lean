-- Prove2me | Theorems.Thm_OAI_TreeEdit_FiniteProbability_probability_union_bound
-- name    : OAI.TreeEdit.FiniteProbability.probability_union_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:41:57.348098+00:00
-- url     : https://prove2.me/theorems/6a3a1ecb-2968-4df0-8bea-32455858d880
-- title:
--   Union bound for the uniform probability on a finite set
-- statement:
--   Let $A$ be a finite set with the uniform probability: for a predicate (event) $E$ on $A$,
--
--   $$\Pr_{a\in A}[E(a)]=\frac{1}{|A|}\sum_{a\in A}\mathbf{1}_{E}(a)=\frac{|\{a\in A: E(a)\}|}{|A|},$$
--
--   where $\mathbf{1}_E(a)$ is $1$ if $E(a)$ holds and $0$ otherwise. Let $I$ be an arbitrary index set, $S\subseteq I$ a finite subset, and $(E_i)_{i\in I}$ a family of events on $A$. Then the probability that at least one event indexed by $S$ occurs is at most the sum of their probabilities:
--
--   $$\Pr_{a\in A}\bigl[\exists\, i\in S:\ E_i(a)\bigr]\ \le\ \sum_{i\in S}\Pr_{a\in A}[E_i(a)].$$
--
--   This is Boole's inequality for uniform finite probability spaces. It is used to bound failure probabilities in random constructions, for instance the probability that some row residue at a node of the random circle-phase tree sees too few good children.
--
--   **Formalization Note** The probability is defined as the uniform mean of the $0$/$1$ indicator, with predicates decided classically. No nonemptiness assumption is needed: if $A$ is empty, Lean's convention $0^{-1}=0$ makes both sides equal to $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/FiniteProbability.lean#L73-L86

import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability

open OAI OAI.TreeEdit OAI.TreeEdit.FiniteProbability
open scoped BigOperators
open Classical

theorem OAI.TreeEdit.FiniteProbability.probability_union_bound {A I : Type*} [Fintype A] (s : Finset I) (E : I → A → Prop) :
    probability (fun a => ∃ i ∈ s, E i a) ≤ ∑ i ∈ s, probability (E i) := by sorry
