-- Prove2me | Theorems.Thm_FullyDynamicCorrelation_VertexUpdates_lemma_8_11
-- name    : FullyDynamicCorrelation.VertexUpdates.lemma_8_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:57:43.273685+00:00
-- url     : https://prove2.me/theorems/466f266c-78b4-4cd7-9074-fdc9c6932418
-- title:
--   Lemma 8.11 — Invariant II: with Φ = Θ(log³ n/ε³) a formation’s budget pays its work and passed-on budgets
-- statement:
--   For every cost constant $\kappa>0$ there is $C_0>0$ such that for every $C_\varphi\ge C_0$, with $\Phi=C_\varphi\log_2^3n/\varepsilon^3$, for every $0<\varepsilon\le1/19000$, $n\ge10000$, valid stream and reachable state, and every formation of a cluster $K$ so far: the work charged to $K$ plus $\Phi$ times the number of budgets $K$ passed on is at most $2.5\varepsilon\Phi|K|$ if $K$ was formed from a vertex of degree at least $10/\varepsilon$, and at most $\Phi$ otherwise.
--
--   Differences from the source:
--   - generalization: the statement holds with high probability over the algorithm’s random choices → it holds on every execution (prefix) of Step from St.init, in which each sparsity test, merge, formation, identification and size estimate returns some outcome allowed by its success guarantee (Lemmas 3.1–3.3, 7.1, Remark 7.1, the acceptance rule of the proof of Lemma 3.2), chosen adversarially; reason: the analysis is deterministic given these local guarantees (p. 11, p. 63, Appendix B p. 71); on the event that every call succeeds the actual execution is one of these, so the source’s claim follows by the union bound of p. 63
--   - encoding: Algorithms 1–7 with O(·) sample sizes and the high-degree sparsity tester of [BDP+25] → each randomized subroutine is represented by its success guarantee; due levels, set-aside processing and qualifying merges are nondeterministic, while batch entries use Finset.toList and refreshments use the specified stack schedule; reason: this fixes an admissible implementation of the unspecified ordering choices; all outcomes of its successful subroutine calls are included, without assuming the structural conclusions
--   - reading: Remark 5.3: due clusters are removed before any merge or formation and all refreshments complete before an operation continues → a maintained cluster whose inc or del reached εc(K), or which became empty, is removed before any other step, and a due cluster’s refreshment runs on top of the task stack; reason: Algorithm 1 (2c) refreshes “at any point”; this order satisfies all three bullets of Remark 5.3 and Lemma 8.1’s discarding of emptied clusters
--   - reading: “we assume there are at least 10000 vertices in the graph” (p. 13) → 10000 ≤ n; reason: n ≥ 10000 is a padded capacity bound, not a restriction on the current graph: the empty start and all small states remain included; the source handles those with its constant-size/offline branch
--   - encoding: vertices of the dynamic graph → names in {0,…,n−1}; a lifetime (name, index of its insertion) distinguishes a name reused after a deletion; reason: at most n vertices are present at any time (Table 1); history counters must not confuse a reinserted name with the deleted vertex
--   - encoding: Algorithm 4 (1): offline O(1)-approximation while the graph has fewer than 300 log⁴ n vertices → the offline returned partition is separate from the maintained decomposition; totalWork reserves κ m (1 + 300(1 + log₂ n)^4)^q for its polynomial work and degree queries; reason: the branch changes the reported clustering but does not replace the maintained cluster/list state (p. 54); its cost must still be included in Theorem 7, and any fixed polynomial implementation and amplification is covered by a fixed q and coefficient
--   - reading: “the algorithmic operations” paid by K → the work charged to K: its formation with identification and the processing of identified vertices, the record bookkeeping of first additions from outside K(t0), and its refreshment (removal, the ε/20 tests, re-entry of the remaining members); reason: the operations the proof of Lemma 8.11 assigns to K; a merge itself spends the added vertex’s budget (Lemma 8.7)
--   - encoding: “Φ = O(log³ n/ε³), with a sufficiently large constant” → ∃ C₀ > 0 ∀ Cφ ≥ C₀, Φ = Cφ log₂³ n/ε³, C₀ depending only on κ; reason: the meaning of “sufficiently large constant”; ε enters only through the explicit power
--   - encoding: time of an operation → the work Step charges, with the per-operation bounds of Lemmas 3.1–3.3, 8.3, 8.4 and one constant κ for the O(·); reason: the paper’s accounting
-- source:
--   Braverman, Dharangutte, Fan, Wang, Xie and Zhou (2026), Fully Dynamic Correlation Clustering with Vertex Updates in Polylogarithmic Update Time, supplied manuscript sha256 07ee1c8f4214025e0b6a81ffc141dbcc4d3bc385abe36d5b298e3ec6037aaab2, Lemma 8.11, p. 61

import Mathlib
import Definitions.Def_FullyDynamicCorrelation_VertexUpdates_Algorithm

namespace FullyDynamicCorrelation.VertexUpdates

open Classical

/-- Lemma 8.11 (p. 61). -/
theorem lemma_8_11 (κ : ℝ) (hκ : 0 < κ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ Cφ : ℝ, C₀ ≤ Cφ →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 19000 → ∀ n : ℕ, 10000 ≤ n →
        ∀ us : List Update, ValidStream n us → ∀ s : St, Reach n ε κ us s →
          ∀ rc ∈ s.formLog,
            (10 / ε ≤ (rc.seedDeg : ℝ) →
              s.attr rc.id + Cφ * lg n ^ 3 / ε ^ 3 * (s.passed rc.id : ℝ) ≤
                (5 / 2) * ε * (Cφ * lg n ^ 3 / ε ^ 3) * (rc.size : ℝ)) ∧
            ((rc.seedDeg : ℝ) < 10 / ε →
              s.attr rc.id + Cφ * lg n ^ 3 / ε ^ 3 * (s.passed rc.id : ℝ) ≤
                Cφ * lg n ^ 3 / ε ^ 3) := by sorry

end FullyDynamicCorrelation.VertexUpdates
