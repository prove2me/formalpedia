-- Prove2me | Theorems.Thm_IncrementalER_lemma_4_8
-- name    : IncrementalER.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:08:15.320205+00:00
-- url     : https://prove2.me/theorems/f021d731-1f1a-459f-8bfc-c09dea1179c4
-- title:
--   Lemma 4.8, p.20 — $\sum_{x\in F}[\ell^G_{Q\cup F}(x)-\ell^G_{Q\cup\{x\}}(x)]_+\le2(|F|-1)$
-- statement:
--   Let $G$ be a connected graph, $Q\neq\emptyset$, and $F\subseteq V\setminus Q$ nonempty. Then
--
--   $$\sum_{x\in F}\big[\ell^G_{Q\cup F}(x)-\ell^G_{Q\cup\{x\}}(x)\big]_+\le2(|F|-1),$$
--
--   where $[y]_+=\max(y,0)$. After adding a set $F$ of terminals, the total increase of leverage mass over the vertices of $F$ is at most $2(|F|-1)$; this powers the batch-update analysis. Connectivity is the paper's standing assumption ("We assume throughout that everywhere we are dealing exclusively with connected graphs", p.10) and is a hypothesis.
--
--   Differences from the source:
--   - encoding: G = (V, E, c) an undirected capacitated multigraph (p.10) → a symmetric nonnegative conductance function with zero diagonal (parallel capacities added, no loops); reason: the Laplacian, effective resistances, leverage degrees and the random walk are unchanged by merging parallel edges; the paper's edges (u, v) join two vertices, and the source never uses loops
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), Lemma 4.8, p.20; Definition 3.5, p.12; connectivity, p.10

import Mathlib
import Definitions.Def_IncrementalER_scCond

namespace IncrementalER

/-- **Lemma 4.8** (total positive increase of leverage degrees when adding a set).

Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, *Incremental All-Pairs Effective Resistance in
Almost-Linear Time*, STOC 2027 submission (manuscript sha256 a0415fd5…), Lemma 4.8, p.20;
Definition 3.5, p.12; connectivity assumption, p.10.

For a connected graph `G`, a nonempty `Q` and a nonempty `F ⊆ V \ Q`,
`∑_{x ∈ F} [ℓ^G_{Q∪F}(x) − ℓ^G_{Q∪{x}}(x)]_+ ≤ 2(|F| − 1)`. -/
theorem lemma_4_8 {V : Type*} [Fintype V] [DecidableEq V] (c : V → V → ℝ) (hc : IsGraph c)
    (hconn : Connected c) (Q F : Finset V) (hQ : Q.Nonempty) (hF : F.Nonempty)
    (hFQ : Disjoint F Q) :
    ∑ x ∈ F, max (levDegT c (Q ∪ F) x - levDegT c (insert x Q) x) 0 ≤
      2 * ((F.card : ℝ) - 1) := by sorry

end IncrementalER
