-- Prove2me | Theorems.Thm_LocalBreadth_lemma_5_4
-- name    : LocalBreadth.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:54:53.798952+00:00
-- url     : https://prove2.me/theorems/922bce9c-1033-4806-9b46-cd6049468485
-- title:
--   Lemma 5.4 — the basic neighborhoods are a basis, and the open sets are those with a finite test at each point
-- statement:
--   Let $\mathcal X$ be a nonempty countable family of infinite subsets of $\mathbb Z$.
--   The basic neighborhoods form a basis of the finite-evidence history topology. Moreover, a set $U$ of histories is open if and only if for every $H\in U$ there is a finite set $F_H\subseteq\mathrm{end}(H)$ such that every $M\in\mathcal X$ with $F_H\subseteq M\subsetneq\mathrm{end}(H)$ satisfies $H^\frown M\in U$.
--
--   This local description of open sets is what every later use of the topology works with.
--
--   Differences from the source:
--   - encoding: one finite set $F_\Gamma$ chosen at each included history → a total rule on all histories; reason: its values at histories never included are unused
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc…), Lemma 5.4, p.25

import Mathlib
import Definitions.Def_LocalBreadth_historyTopology

open scoped Topology

namespace LocalBreadth

/-- Lemma 5.4. Kleinberg, Wei, STOC 2027 submission (manuscript sha256 f924cbfc…), p.25. The basic
neighborhoods form a basis of the history topology, and `U` is open iff every `H ∈ U` has a finite
`F_H ⊆ end(H)` such that every `M ∈ X` with `F_H ⊆ M ⊊ end(H)` has `H⌢M ∈ U`. -/
theorem lemma_5_4 (X : Set (Set ℤ)) (hne : X.Nonempty) (hc : X.Countable) (hinf : ∀ L ∈ X, L.Infinite) :
    @TopologicalSpace.IsTopologicalBasis (History X) (historyTopology X) (basicSets X) ∧
    ∀ U : Set (History X), IsOpen[historyTopology X] U ↔
      ∀ H ∈ U, ∃ F : Finset ℤ, (F : Set ℤ) ⊆ H.last ∧
        ∀ (M : Set ℤ) (hM : M ∈ X) (hlt : M ⊂ H.last), (F : Set ℤ) ⊆ M → H.snoc M hM hlt ∈ U := by sorry

end LocalBreadth
