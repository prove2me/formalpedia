-- Prove2me | Theorems.Thm_GeoSemialgCSP_lemma_3_1
-- name    : GeoSemialgCSP.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:51:34.196542+00:00
-- url     : https://prove2.me/theorems/ef692eed-1a28-479e-8c0b-1bf24896d5ae
-- title:
--   Lemma 3.1 — geometric predicates have cousins homomorphisms
-- statement:
--   Let $P$ be a geometric semialgebraic predicate of arity $k\ge2$ on $\mathbb R^d$, with at least one satisfying tuple. Then there is a map $\phi$ from the nodes of the universal ordered $k$-ary tree to $\mathbb R^d$ such that for every tuple of nodes $l_1,\dots,l_k$,
--   $$\mathrm{cousins}(l_1,\dots,l_k)=1\ \Longrightarrow\ P(\phi(l_1),\dots,\phi(l_k))=1 .$$
--   Restricting $\phi$ to a finite ordered $k$-ary tree $T$, embedded in the universal tree, gives a map $T\to\mathbb R^d$ that sends every cousins tuple of leaves to a satisfying tuple of $P$.
--
--   The lemma supplies property (2) for geometric predicates, which reduces Corollary 3.2 to Theorem 6.1.
--
--   Differences from the source:
--   - generalization: a finite ordered k-ary tree T and ϕ : T → ℝ^d, for cousins tuples of leaves → one ϕ : List (Fin k) → E d on the universal ordered k-ary tree, for every cousins tuple of nodes; reason: every finite ordered k-ary tree embeds in the universal one preserving cousins tuples; restricting ϕ gives the printed lemma
--   - reading: a geometric semialgebraic predicate → S.Nonempty added; reason: footnote 1 (p.1): all predicates are assumed to have a satisfying assignment; for S = ∅ the printed lemma is false (a root with k leaf children is a cousins tuple)
--   - encoding: a predicate P : (ℝ^d)^k → {0,1}, semialgebraic in the k·d coordinates → its accepting set S ⊆ (EuclideanSpace ℝ (Fin d))^k, semialgebraic through finProdFinEquiv; reason: the same predicate; P(x) = 1 iff x ∈ S
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), Lemma 3.1, p.9 (PDF p.10)

import Mathlib
import Definitions.Def_GeoSemialgCSP_E
import Definitions.Def_GeoSemialgCSP_IsSemialgebraicPred
import Definitions.Def_GeoSemialgCSP_IsGeometric
import Definitions.Def_GeoSemialgCSP_cousins

namespace GeoSemialgCSP

/-- **Lemma 3.1 (cousins homomorphism of a geometric predicate).** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), Lemma 3.1, printed p.9
(PDF p.10): for a geometric semialgebraic predicate `P` and a finite ordered `k`-ary tree `T` there
is `ϕ : T → ℝ^d` such that `cousins(l₁, …, l_k) = 1` implies `P(ϕ(l₁), …, ϕ(l_k)) = 1`.

**Formalization Note.** One map `ϕ` on the universal ordered `k`-ary tree (words `List (Fin k)`),
valid for every cousins tuple of nodes; restricting it along the embedding of a finite tree gives
the printed lemma. `S.Nonempty` is footnote 1 (p.1): predicates are assumed satisfiable. `k ≥ 2` is
the §3 setup. -/
theorem lemma_3_1 {k d : ℕ} (hk : 2 ≤ k) (S : Set (Fin k → E d)) (hsa : IsSemialgebraicPred S)
    (hgeo : IsGeometric S) (hne : S.Nonempty) :
    ∃ ϕ : List (Fin k) → E d, ∀ l : Fin k → List (Fin k), cousins l → ϕ ∘ l ∈ S := by sorry

end GeoSemialgCSP
