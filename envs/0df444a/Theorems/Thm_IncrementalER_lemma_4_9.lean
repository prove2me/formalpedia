-- Prove2me | Theorems.Thm_IncrementalER_lemma_4_9
-- name    : IncrementalER.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:07:46.035302+00:00
-- url     : https://prove2.me/theorems/1d12a5a1-512c-42a6-bdee-cacac27e6149
-- title:
--   Lemma 4.9, p.21 — $\mathbb E_D[\sum_vp(v)[g_Q(v;D)]_+]\le4$
-- statement:
--   Let $G$ be a connected graph, $Q\neq\emptyset$, $S\subseteq V$ with $|S|=r\ge1$, and $p$ a probability distribution on $V$. Sample $X_1,\dots,X_r$ i.i.d. from $p$ and let $D=S\cup\{X_1,\dots,X_r\}$. Then
--
--   $$\mathbb E_D\Big[\sum_{v\in V}p(v)\,[g_Q(v;D)]_+\Big]\le4,$$
--
--   where $g_Q(v;D)=f_{Q\cup D}(v)-f_Q(v)$ for $v\notin Q\cup D$ and $0$ otherwise. This is the batch analogue of Lemma 4.4. Connectivity is the paper's standing assumption ("We assume throughout that everywhere we are dealing exclusively with connected graphs", p.10) and is a hypothesis.
--
--   Differences from the source:
--   - encoding: G = (V, E, c) an undirected capacitated multigraph (p.10) → a symmetric nonnegative conductance function with zero diagonal (parallel capacities added, no loops); reason: the Laplacian, effective resistances, leverage degrees and the random walk are unchanged by merging parallel edges; the paper's edges (u, v) join two vertices, and the source never uses loops
--   - encoding: E_D over i.i.d. samples X_1, …, X_r ∼ p → the finite sum over X : Fin r → V weighted by ∏_i p(X_i); reason: the definition of the expectation for finitely many independent draws on a finite set
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), Lemma 4.9, p.21; g_Q(v; D), p.19; connectivity, p.10

import Mathlib
import Definitions.Def_IncrementalER_scCond

namespace IncrementalER

/-- **Lemma 4.9** (average positive batch cost after sampling `|S|` terminals).

Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, *Incremental All-Pairs Effective Resistance in
Almost-Linear Time*, STOC 2027 submission (manuscript sha256 a0415fd5…), Lemma 4.9, p.21; `g_Q(v; D)`, p.19; connectivity assumption, p.10.

Let `G` be a connected graph, `Q ≠ ∅`, `S ⊆ V` with `|S| = r ≥ 1`, and `p` a probability
distribution on `V`. Sample `X_1, …, X_r` i.i.d. from `p` and let `D = S ∪ {X_1, …, X_r}`.
Then `E_D[∑_v p(v) [g_Q(v; D)]_+] ≤ 4`.

**Formalization Note.** The sample is `X : Fin r → V` with probability `∏_i p(X_i)`; the
expectation is the finite sum over all samples. `S` may meet `Q`. -/
theorem lemma_4_9 {V : Type*} [Fintype V] [DecidableEq V] (c : V → V → ℝ) (hc : IsGraph c)
    (hconn : Connected c) (Q S : Finset V) (hQ : Q.Nonempty) (hS : 1 ≤ S.card) (p : V → ℝ)
    (hp0 : ∀ v, 0 ≤ p v) (hp1 : ∑ v, p v = 1) :
    ∑ X : Fin S.card → V, (∏ i, p (X i)) *
        ∑ v, p v * max (gQ c Q (S ∪ Finset.univ.image X) v) 0 ≤ 4 := by sorry

end IncrementalER
