-- Prove2me | Theorems.Thm_GirthBethe_Sharp_edge_information_inequalities
-- name    : GirthBethe.Sharp.edge_information_inequalities
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:19:41.03452+00:00
-- url     : https://prove2.me/theorems/170a6d0d-bbda-4ea1-a9fb-0c720c70bcf1
-- title:
--   Lemma 4.2 — $J^-_v\le J^+_v$ and $J^-_e\le\sum_{f\ni v,f\ne e}J^+_f$
-- statement:
--   Let $G=(L\sqcup R,E)$ be a finite bipartite graph, $\mu$ a probability law on its perfect matchings, $\star\in L$, and $J^\pm_e$, $J^\pm_v$ the weights of Definition 4.1. Then for every vertex $v$ and every edge $e\ni v$,
--   $$J^-_v\le J^+_v,\qquad J^-_e\le\sum_{f\ni v,\ f\neq e}J^+_f .$$
--
--   These are the only properties of the weights used in the construction of the auxiliary flow.
--
--   Differences from the source:
--   - encoding: a bipartite graph G = (L ⊔ R, E) with |L| = |R| = n and its perfect matchings → finite types L, R, an edge finset E ⊆ L × R (a simple bipartite graph on L ⊕ R), and perfect matchings recorded as bijections σ : L ≃ R with (u, σ u) ∈ E for all u; |L| = |R| is not a separate hypothesis; reason: a perfect matching is the same as such a bijection; a probability law on perfect matchings exists only when one exists, which forces |L| = |R|
--   - encoding: a probability distribution μ on the perfect matchings, p_e = P(e ∈ M), X_u the partner of u → μ ∈ stdSimplex ℝ (PerfMatching E) (arbitrary, zeros allowed); p = edgeMarg μ, X_u = matchX u; reason: the same finite probability law and the same random variables
--   - encoding: J_e^± with KL from Definition 2.5 (values in [0, +∞]) → real J_e^± obtained from the extended-real divergence klDiv by EReal.toReal, with the zero conventions of Definition 4.1; reason: a posterior given an event of positive probability is absolutely continuous with respect to the prior, so the divergence is finite and toReal does not change its value
--   - generalization: the standing setting of §3: even g ≥ 4 and G of girth at least g → no hypothesis on g or on the girth of G; reason: the proof uses only that M is a perfect matching; adding the standing hypotheses gives the source statement
--   - encoding: conditional laws L(X_⋆ | E_e = b) in Definition 4.1 → condLaw uses the unconditional law when P(E_e = b) = 0; reason: Definition 4.1 sets that weighted KL contribution to zero; at positive-probability events the usual conditional law is used
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #705 (October 2026), p. 11, Lemma 4.2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/705.pdf

import Mathlib
import Definitions.Def_GirthBethe_Sharp_MatchingLaw

open Finset

namespace GirthBethe.Sharp

open scoped Classical in
/-- Lemma 4.2: `J_v^- ≤ J_v^+` and `J_e^- ≤ ∑_{f ∋ v, f ≠ e} J_f^+` for every vertex `v` and edge `e ∋ v`. -/
theorem edge_information_inequalities {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (E : Finset (L × R))
    (μ : PerfMatching E → ℝ) (hμ : μ ∈ stdSimplex ℝ (PerfMatching E)) (star : L) (v : L ⊕ R) :
    jMinusV μ star v ≤ jPlusV μ star v ∧
      ∀ e : Edge E, Inc v e.1 →
        jMinus μ star e ≤ ∑ f with Inc v f.1 ∧ f ≠ e, jPlus μ star f := by sorry

end GirthBethe.Sharp
