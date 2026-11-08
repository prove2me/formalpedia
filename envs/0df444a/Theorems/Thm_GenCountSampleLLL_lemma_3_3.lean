-- Prove2me | Theorems.Thm_GenCountSampleLLL_lemma_3_3
-- name    : GenCountSampleLLL.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:39:39.726545+00:00
-- url     : https://prove2.me/theorems/080f5017-1584-403c-8ec9-b14d9fe37a83
-- title:
--   Lemma 3.3, p.13 — $\sum_{S\ni a,\ H[S]\text{ connected}}\prod_{v\in S}w_v\le\alpha z_a/(1-z_a)$
-- statement:
--   Let $H=(V,E)$ be a finite simple graph and $0<\alpha<1$. Suppose $z\in(0,1)^V$ and $w\in[0,\infty)^V$ satisfy
--   $$
--   w_v\le\alpha z_v\prod_{u\in N_H(v)}(1-z_u)\qquad(v\in V).
--   $$
--   Then for every $a\in V$,
--   $$
--   \sum_{\substack{S\subseteq V,\ a\in S\\ H[S]\text{ connected}}}\ \prod_{v\in S}w_v\le\alpha\frac{z_a}{1-z_a}.
--   $$
--
--   This bound controls every sum over connected sets of active constraints in the analysis.
--
--   Differences from the source: none.
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, arXiv:2609.23671 (held file sha256 cd449f83…), Lemma 3.3, p.13

import Mathlib

set_option autoImplicit false

open scoped BigOperators

open Classical

namespace GenCountSampleLLL

/-- Lemma 3.3, p.13 (Jain, Mizgerd, Pham, *A general counting and sampling Lovász local lemma*, arXiv:2609.23671 (held file sha256 cd449f83…)). Let `H = (V, E)` be a finite simple graph and
`0 < α < 1`. If `z ∈ (0,1)^V` and `w ∈ [0,∞)^V` satisfy `w_v ≤ α z_v ∏_{u ∈ N_H(v)} (1 − z_u)` for
every `v ∈ V`, then for every `a ∈ V`,
`Σ_{S ⊆ V, a ∈ S, H[S] connected} ∏_{v ∈ S} w_v ≤ α z_a/(1 − z_a)`.

**Formalization Note.** `N_H(v)` is the open neighbourhood `H.neighborFinset v`; `H[S]` is the
induced subgraph `H.induce S`. -/
theorem lemma_3_3 {V : Type} [Fintype V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (α : ℝ) (hα : 0 < α ∧ α < 1) (z w : V → ℝ)
    (hz : ∀ v, 0 < z v ∧ z v < 1) (hw : ∀ v, 0 ≤ w v)
    (hcond : ∀ v, w v ≤ α * z v * ∏ u ∈ H.neighborFinset v, (1 - z u)) (a : V) :
    ∑ S ∈ Finset.univ.filter
        (fun S : Finset V => a ∈ S ∧ (H.induce (S : Set V)).Connected), ∏ v ∈ S, w v ≤
      α * z a / (1 - z a) := by sorry

end GenCountSampleLLL
