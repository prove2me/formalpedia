-- Prove2me | Theorems.Thm_IncrementalER_lemma_4_13
-- name    : IncrementalER.lemma_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:08:14.612498+00:00
-- url     : https://prove2.me/theorems/ce0c2c26-8de0-4755-b96e-25a86ee3949d
-- title:
--   Lemma 4.13, p.26 — $\ell^G_{T_1\cup\dots\cup T_k\cup\{v\}}(v)\le\sum_i\ell^G_{T_i\cup\{v\}}(v)$
-- statement:
--   Let $G$ be a connected graph and $T_1,\dots,T_k\subseteq V$. Then for every $v\in V$,
--
--   $$\ell^G_{T_1\cup T_2\cup\dots\cup T_k\cup\{v\}}(v)\le\sum_{i=1}^k\ell^G_{T_i\cup\{v\}}(v).$$
--
--   The insertion cost of a vertex with respect to a union of terminal sets is at most the sum of its costs with respect to the parts; the paper uses this to compose terminal sets in the proof of Theorem 2.1. Connectivity is the paper's standing assumption ("We assume throughout that everywhere we are dealing exclusively with connected graphs", p.10) and is a hypothesis.
--
--   Differences from the source:
--   - encoding: G = (V, E, c) an undirected capacitated multigraph (p.10) → a symmetric nonnegative conductance function with zero diagonal (parallel capacities added, no loops); reason: the Laplacian, effective resistances, leverage degrees and the random walk are unchanged by merging parallel edges; the paper's edges (u, v) join two vertices, and the source never uses loops
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), Lemma 4.13, p.26; Definition 3.5, p.12; connectivity, p.10

import Mathlib
import Definitions.Def_IncrementalER_scCond

namespace IncrementalER

/-- **Lemma 4.13** (subadditivity of the leverage degree over terminal sets).

Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, *Incremental All-Pairs Effective Resistance in
Almost-Linear Time*, STOC 2027 submission (manuscript sha256 a0415fd5…), Lemma 4.13, p.26; Definition 3.5, p.12; connectivity assumption, p.10.

For a connected graph `G`, sets `T_1, …, T_k ⊆ V` and any `v ∈ V`,
`ℓ^G_{T_1 ∪ ⋯ ∪ T_k ∪ {v}}(v) ≤ ∑_{i=1}^k ℓ^G_{T_i ∪ {v}}(v)`.

**Formalization Note.** The sets are indexed by `Fin k`; `k = 0` and empty `T_i` are allowed (then
`ℓ^G_{{v}}(v) = 0`). -/
theorem lemma_4_13 {V : Type*} [Fintype V] [DecidableEq V] (c : V → V → ℝ) (hc : IsGraph c)
    (hconn : Connected c) (k : ℕ) (T : Fin k → Finset V) (v : V) :
    levDegT c (insert v (Finset.univ.biUnion T)) v ≤ ∑ i, levDegT c (insert v (T i)) v := by sorry

end IncrementalER
