-- Prove2me | Theorems.Thm_LocalProbeMIS871_Greedy_theorem_3_1
-- name    : LocalProbeMIS871.Greedy.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T01:52:16.634952+00:00
-- url     : https://prove2.me/theorems/d5685fc2-a8cf-4047-ace1-1d791d9927a3
-- title:
--   Theorem 3.1 — An absolute degree-six probe tail
-- statement:
--   Assign every vertex an independent uniform rank in $(0,1)$ under $\mu_n$, including the root. Let $Q_G(v,r)$ count the degree probe and complete adjacency list of every fresh evaluation in the specified early-stopping algorithm.
--
--   There exists one absolute $C>0$ such that for every finite simple labeled graph $G$, every integer degree bound $\Delta\ge2$, every fixed adjacency-list ordering, every root $v$, and every real $\lambda\ge0$,
--
--   $$\Pr_{r\sim\mu_n}\{Q_G(v,r)>C\Delta^6(1+\lambda)\}\le e^{-\lambda}.$$
--
--   The same constant precedes all graph, ordering, root, and tail parameters. The cost counts degree-plus-list probes of the actual cached run.
--
--   Differences from the source:
--   - encoding: finite labeled graph and real rank assignment → Fin n, lexicographic real-rank/label keys, and computed cached execution; reason: zero-based labels enumerate exactly the same finite graphs and implement the source tie rule without adding a hypothesis
--   - encoding: an absolute O-constant and probability over the original uniform ranks → an existential positive real C before every input, and event measure under rankLaw; reason: the all-uniform rank law and real tail parameter, including zero, are retained exactly
-- source:
--   Peter Kiss, Yuichi Yoshida, The Local Probe Complexity of Maximal Independent Set, STOC 2027 submission #871 (October 2026), p. 11, PDF p. 13, Theorem 3.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/871.pdf

import Definitions.Def_LocalProbeMIS871_Greedy_Model

open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false

namespace LocalProbeMIS871.Greedy

/-- Theorem 3.1, printed p.11 / PDF13; the original all-uniform law and actual probes. -/
theorem theorem_3_1 : ∃ C : ℝ, 0 < C ∧
    ∀ (n Δ : ℕ), 2 ≤ Δ → ∀ G : SimpleGraph (Fin n), (∀ u, G.degree u ≤ Δ) →
    ∀ lists : AdjacencyLists G, ∀ v : Fin n, ∀ ell : ℝ, 0 ≤ ell →
      rankLaw n {r | C * (Δ : ℝ) ^ (6 : ℕ) * (1 + ell) < (Q G lists v r : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-ell)) := by sorry

end LocalProbeMIS871.Greedy
