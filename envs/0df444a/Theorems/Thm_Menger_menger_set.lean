-- Prove2me | Theorems.Thm_Menger_menger_set
-- name    : Menger.menger_set
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T13:31:41.357239+00:00
-- url     : https://prove2.me/theorems/627d82b4-76e4-4da5-8269-6df695702902
-- title:
--   Menger's theorem (set form)
-- statement:
--   **Menger's theorem, set form.** Let $G$ be a graph, $S$ a finite set of vertices, and $A,B\subseteq S$. Suppose every $A$–$B$ separator $X\subseteq S$ (a set meeting every $A$–$B$ path inside $S$) has at least $k$ vertices. Then $G$ contains $k$ pairwise vertex-disjoint $A$–$B$ paths inside $S$:
--
--   $$\Bigl(\forall X\subseteq S,\ X\text{ separates }A\text{ from }B\ \Rightarrow\ |X|\ge k\Bigr)\ \Longrightarrow\ \text{there are }k\text{ disjoint }A\text{–}B\text{ paths in }G[S].$$
--
--   Together with the trivial converse (a separator meets each path of a linkage) this says that the maximum number of disjoint $A$–$B$ paths equals the minimum size of an $A$–$B$ separator. The vertex form of Menger's theorem for two vertices, and Whitney's characterization of $n$-connected graphs, follow from it.
--
--   **Formalization Note** Paths are duplicate-free lists of vertices, so a single vertex of $A\cap B$ is a path, and separators may contain vertices of $A\cap B$. The set $S$ plays the role of the ambient graph $G[S]$; taking $S$ to be the whole vertex set gives the usual statement.
-- source:
--   R. Diestel, Graph Theory, 5th ed., Springer GTM 173, Section 3.3, Theorem 3.3.1 (Menger 1927); the proof formalized follows the argument via a separator different from A and B, and edge deletion, in Diestel's text.

import Mathlib
import Definitions.Def_Menger_Linkage

namespace Menger

theorem menger_set {V : Type*} [DecidableEq V] (G : SimpleGraph V) (S A B : Finset V)
    (hA : A ⊆ S) (hB : B ⊆ S) (k : ℕ)
    (hsep : ∀ X : Finset V, X ⊆ S → IsABSep G S A B X → k ≤ X.card) :
    HasLinkage G S A B k := by sorry

end Menger
