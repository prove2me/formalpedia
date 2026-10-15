-- Prove2me | Theorems.Thm_OAI_InfiniteMatroidCounterexample_BasisSystem_insert_indep_of_not_base
-- name    : OAI.InfiniteMatroidCounterexample.BasisSystem.insert_indep_of_not_base
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T06:03:51.781057+00:00
-- url     : https://prove2.me/theorems/dd3553cf-f00d-469a-b4f3-9b657c0086f0
-- title:
--   In a matroid built from a basis system, an independent non-base stays independent after adding any element
-- statement:
--   Let $\alpha$ be a type and let $\mathcal B$ be a *basis system* on $\alpha$, i.e. a family of subsets of $\alpha$ such that
--   $\mathcal B$ is nonempty; $\mathcal B$ is an antichain ($B,C\in\mathcal B$ and $B\subseteq C$ imply $B=C$); $\mathcal B$ is closed under complements ($B\in\mathcal B$ implies $\alpha\setminus B\in\mathcal B$); $\mathcal B$ is closed under single exchanges (if $B\in\mathcal B$, $f\in B$ and $e\notin B$, then $(B\setminus\{f\})\cup\{e\}\in\mathcal B$); and $\mathcal B$ satisfies the interval alternative (whenever $I\subseteq Y\subseteq\alpha$ and $Y\setminus I$ is infinite, some $B\in\mathcal B$ satisfies $B\subseteq I$, or $I\subseteq B\subseteq Y$, or $Y\subseteq B$). Let $M=M(\mathcal B)$ be the associated (possibly infinite) matroid: its ground set is all of $\alpha$, its bases are exactly the members of $\mathcal B$, and a set is independent in $M$ if and only if it is contained in some member of $\mathcal B$.
--
--   **Theorem.** Let $I\subseteq\alpha$ be independent in $M$ but not a base of $M$. Then for every element $e\in\alpha$ the set $I\cup\{e\}$ is independent in $M$:
--
--   $$I\ \text{independent in } M,\quad I\notin\mathcal B\quad\Longrightarrow\quad I\cup\{e\}\ \text{independent in } M\ \text{ for every } e\in\alpha .$$
--
--   In an arbitrary matroid an independent set that is not a base can be enlarged by *some* element; here it can be enlarged by *every* element. Combined with the existence of maximal independent subsets, this shows that $M(\mathcal B)$ is uniform in the sense that every subset $X\subseteq\alpha$ is independent or spanning: a maximal independent subset of $X$ is either a base, and then $X$ is spanning, or it absorbs every element of $X$ and hence equals $X$. In the counterexample this is how the self-dual matroid on $E_0$ obtained from a basis system is shown to be uniform, a property required of it in the main statement.
--
--   **Formalization Note** The basis system is `S : BasisSystem α`, a structure with fields `bases`, `nonempty`, `antichain`, `compl_closed`, `swap` and `intervals`; the matroid is `S.matroid`, built with Mathlib's `Matroid.ofBase` on ground set `univ`, and the statement is phrased with `S.matroid.Indep` and `S.matroid.IsBase`. The case $e\in I$ is included (and trivial).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/InfiniteMatroid/Matroid.lean#L97-L111

import Mathlib
import Definitions.Def_InfiniteMatroidCorollaries
import Definitions.Def_OAI_Combinatorics_InfiniteMatroid_Matroid__InfiniteMatroidCorollaries

open OAI OAI.InfiniteMatroidCounterexample OAI.InfiniteMatroidCounterexample.BasisSystem
open Set Matroid
variable {α : Type*} (S : BasisSystem α)

theorem OAI.InfiniteMatroidCounterexample.BasisSystem.insert_indep_of_not_base {I : Set α} (hI : S.matroid.Indep I)
    (hnot : ¬ S.matroid.IsBase I) (e : α) : S.matroid.Indep (insert e I) := by sorry
