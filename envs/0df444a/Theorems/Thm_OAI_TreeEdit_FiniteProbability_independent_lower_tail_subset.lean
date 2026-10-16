-- Prove2me | Theorems.Thm_OAI_TreeEdit_FiniteProbability_independent_lower_tail_subset
-- name    : OAI.TreeEdit.FiniteProbability.independent_lower_tail_subset
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:43:58.803264+00:00
-- url     : https://prove2.me/theorems/7de4e0fd-65ea-4738-8775-6ada8abc42fe
-- title:
--   Fewer than $n/4$ successes among independent events of probability at least $4/5$ has probability at most $(4/5)^n$
-- statement:
--   Let $I$ be a finite index set and, for each $i\in I$, let $A_i$ be a finite nonempty set and $E_i\subseteq A_i$ an event. Draw $a=(a_i)_{i\in I}$ uniformly at random from the product $\prod_{i\in I}A_i$; equivalently, the coordinates $a_i$ are independent and each $a_i$ is uniform on $A_i$. Let $S\subseteq I$ and let $n$ be a natural number with $n\le|S|$, and assume that each event indexed by $S$ is likely: $\Pr_{a_i\in A_i}[a_i\in E_i]\ge 4/5$ for every $i\in S$. Then
--
--   $$
--   \Pr_{a\in\prod_{i}A_i}\Bigl[\,4\cdot\#\{i\in I: a_i\in E_i\}<n\,\Bigr]\le\Bigl(\frac45\Bigr)^{n}.
--   $$
--
--   So the probability that fewer than $n/4$ of the events occur is exponentially small in $n$. The count runs over all $i\in I$, while the hypothesis is only imposed for $i\in S$; events outside $S$ are unrestricted. This Chernoff-type estimate is used to show that in a random configuration a constant fraction of the children of a node are good, except with probability exponentially small in the number of children.
--
--   **Formalization Note** `probability` is the uniform average of an indicator over a finite type; the product is the dependent function type `(i : I) → A i` with its product `Fintype` structure, and $S$ is a `Finset I`. The comparison $4\cdot\#\{\dots\}<n$ is between natural numbers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/FiniteProbability.lean#L248-L292

import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability

open OAI OAI.TreeEdit OAI.TreeEdit.FiniteProbability
open scoped BigOperators
open Classical

theorem OAI.TreeEdit.FiniteProbability.independent_lower_tail_subset {I : Type*} [Fintype I] {A : I → Type*}
    [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] (E : ∀ i, A i → Prop)
    (s : Finset I) {n : ℕ} (hn : n ≤ s.card)
    (hE : ∀ i ∈ s, (4 : ℝ) / 5 ≤ probability (E i)) :
    probability (fun a : ∀ i, A i =>
      4 * (Finset.univ.filter (fun i => E i (a i))).card < n) ≤ (4 / 5 : ℝ) ^ n := by sorry
