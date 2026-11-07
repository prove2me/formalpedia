-- Prove2me | Theorems.Thm_LocalBreadth_lemma_5_6
-- name    : LocalBreadth.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:56:01.496489+00:00
-- url     : https://prove2.me/theorems/532f3472-3daa-428f-b912-3419839beadf
-- title:
--   Lemma 5.6 — closure in the history topology is witnessed by obstruction trees
-- statement:
--   Let $\mathcal X$ be a nonempty countable family of infinite subsets of $\mathbb Z$.
--   Let $A\in\mathcal X$, let $D$ be a set of histories beginning at $A$, and let $H$ be a history beginning at $A$. Then $H$ belongs to the closure of $D$ if and only if there is an admissible obstruction tree rooted at $\mathrm{end}(H)$ such that every root-to-leaf path, when appended to $H$ with the common language written once, produces a history in $D$.
--
--   This is the bridge between the topological and the combinatorial formula.
--
--   Differences from the source:
--   - encoding: closure taken in $\mathcal H_A$ → closure taken in the space of all histories; reason: $\mathcal H_A$ is open and closed (p.27), and $D\subseteq\mathcal H_A$
--   - encoding: a countable rooted tree with no infinite path → the inductive type `ObsTree` with `ℕ`-indexed children; reason: same trees up to repeated subtrees, which do not change the path set
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc…), Lemma 5.6, p.27

import Mathlib
import Definitions.Def_LocalBreadth_historyTopology
import Definitions.Def_LocalBreadth_bTop
import Definitions.Def_LocalBreadth_ObsTree

open scoped Topology

namespace LocalBreadth

/-- Lemma 5.6. Kleinberg, Wei, STOC 2027 submission (manuscript sha256 f924cbfc…), p.27. For
`D ⊆ ℋ_A` and `H ∈ ℋ_A`, `H` belongs to the closure of `D` iff there is an admissible obstruction tree
rooted at `end(H)` such that every root-to-leaf path, when appended to `H`, produces a history in `D`.

**Formalization Note.** The closure is taken in `ℋ`; `ℋ_A` is open and closed there (p.27), so it agrees
with the closure in `ℋ_A` on subsets of `ℋ_A`. Appending writes the common language once: `H ++ p.tail`. -/
theorem lemma_5_6 (X : Set (Set ℤ)) (hne : X.Nonempty) (hc : X.Countable) (hinf : ∀ L ∈ X, L.Infinite)
    (A : Set ℤ) (hA : A ∈ X) (D : Set (History X)) (hD : D ⊆ historiesFrom X A)
    (H : History X) (hH : H ∈ historiesFrom X A) :
    H ∈ closure[historyTopology X] D ↔
      ∃ T : ObsTree, T.Admissible X ∧ T.label = H.last ∧
        ∀ p ∈ T.paths, ∃ G ∈ D, G.chain = H.chain ++ p.tail := by sorry

end LocalBreadth
