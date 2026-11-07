-- Prove2me | Theorems.Thm_IncrementalER_lemma_4_4
-- name    : IncrementalER.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:07:51.848503+00:00
-- url     : https://prove2.me/theorems/3fca1ed5-8b5c-433a-a00e-752c795ace2b
-- title:
--   Lemma 4.4, p.17 — $|Q|\le2r$ and $\mathbb E_Q[\sum_vp(v)f_Q(v)]\le4$
-- statement:
--   Let $G$ be a connected graph, $S\neq\emptyset$ a set of $r=|S|$ vertices, and $p$ a probability distribution on $V$. Sample $X_1,\dots,X_r$ independently from $p$ and put $Q=S\cup\{X_1,\dots,X_r\}$. Then $|Q|\le2r$ and
--
--   $$\mathbb E_Q\Big[\sum_{v\in V}p(v)\,f_Q(v)\Big]\le4,$$
--
--   where $f_Q(v)=\ell^G_{Q\cup\{v\}}(v)$ for $v\notin Q$ and $f_Q(v)=0$ for $v\in Q$. This is the oracle guarantee of the initialization MWU. Connectivity is the paper's standing assumption ("We assume throughout that everywhere we are dealing exclusively with connected graphs", p.10) and is a hypothesis.
--
--   Differences from the source:
--   - encoding: G = (V, E, c) an undirected capacitated multigraph (p.10) → a symmetric nonnegative conductance function with zero diagonal (parallel capacities added, no loops); reason: the Laplacian, effective resistances, leverage degrees and the random walk are unchanged by merging parallel edges; the paper's edges (u, v) join two vertices, and the source never uses loops
--   - encoding: E_Q over independent samples X_1, …, X_r ∼ p → the finite sum over X : Fin r → V weighted by ∏_i p(X_i); reason: the definition of the expectation for finitely many independent draws on a finite set
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), Lemma 4.4, p.17; insertion cost f_T, p.14; connectivity, p.10

import Mathlib
import Definitions.Def_IncrementalER_scCond

namespace IncrementalER

/-- **Lemma 4.4** (average insertion cost after sampling `|S|` terminals).

Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, *Incremental All-Pairs Effective Resistance in
Almost-Linear Time*, STOC 2027 submission (manuscript sha256 a0415fd5…), Lemma 4.4, p.17; the insertion cost `f_T`, p.14; connectivity assumption, p.10.

Let `G` be a connected graph, `S ≠ ∅` with `r = |S|`, and `p` a probability distribution on
`V`. Sample `X_1, …, X_r` independently from `p` and put `Q = S ∪ {X_1, …, X_r}`. Then
`|Q| ≤ 2r` and `E_Q[∑_v p(v) f_Q(v)] ≤ 4`.

**Formalization Note.** The sample is `X : Fin r → V` with probability `∏_i p(X_i)`, and the
expectation is the finite sum over all samples. `|Q| ≤ 2r` holds for every sample. -/
theorem lemma_4_4 {V : Type*} [Fintype V] [DecidableEq V] (c : V → V → ℝ) (hc : IsGraph c)
    (hconn : Connected c) (S : Finset V) (hS : S.Nonempty) (p : V → ℝ) (hp0 : ∀ v, 0 ≤ p v)
    (hp1 : ∑ v, p v = 1) :
    (∀ X : Fin S.card → V, (S ∪ Finset.univ.image X).card ≤ 2 * S.card) ∧
      ∑ X : Fin S.card → V, (∏ i, p (X i)) *
          ∑ v, p v * insCost c (S ∪ Finset.univ.image X) v ≤ 4 := by sorry

end IncrementalER
