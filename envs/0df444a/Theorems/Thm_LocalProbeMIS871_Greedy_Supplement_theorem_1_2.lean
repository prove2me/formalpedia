-- Prove2me | Theorems.Thm_LocalProbeMIS871_Greedy_Supplement_theorem_1_2
-- name    : LocalProbeMIS871.Greedy.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:05:32.525195+00:00
-- url     : https://prove2.me/theorems/b893c939-6212-4360-b24d-28885411ab4d
-- title:
--   Theorem 1.2 — Companion lower bound for arbitrary stateless MIS LCAs
-- statement:
--   There exist absolute $c>0$ and an integer $\Delta_0\ge2$ such that, for every integer $\Delta\ge\Delta_0$ and every possibly randomized adaptive stateless MIS LCA $A$ with any input-independent shared tape law, if $A$ is zero-error correct on every finite simple labeled graph of maximum degree at most $\Delta$ and every fixed adjacency-list ordering, there exist $n\ge1$, a graph $G$ on $n$ labels with maximum degree at most $\Delta$, a valid list ordering $L$, and a vertex $v$, such that
--
--   $$\Pr_r\left[Q_A(G,L,v;r)\ge c\Delta^{3/2}\right]\ge\frac1{16}.$$
--
--   The graph, labels, list order and root are fixed before the tape is sampled. Only the tape is random in this probability. The constants precede the algorithm, its tape space and law, and every input. The algorithm may inspect its entire tape, probe any vertex adaptively, cache within a query and perform unlimited free local computation. Each repeated degree or individual-neighbor call contributes one to $Q_A$.
--
--   This companion theorem gives a constant-probability degree-dependent obstruction for all zero-error stateless MIS LCAs, independently of the published randomized-greedy upper-bound goal. It is the tail lower bound itself.
--
--   **Formalization Note** Equation (47), printed p.33 / PDF35, supplies probability $1/16$. For the constant $C$ of Lemma 4.3, the proof permits $a=1/(64\max\{C,1\})$ and $c=a/2$ once $\Delta$ is sufficiently large. Lean retains the existential positive $c$ and does not invent a numerical degree threshold. The extended probe count agrees with the finite actual count on the probability-one simultaneous termination event; off that event no termination is imposed.
--
--   Differences from the source:
--   - encoding: vertices labeled in [n] → vertices represented by Fin n; reason: adding one to each label is a bijection and preserves all graph and oracle information
--   - encoding: Ω(Δ^(3/2)) with constant probability → there is an absolute positive c with probability at least 1/16 of at least cΔ^(3/2) probes; reason: the source proof at Eq. (47) gives this probability witness and c=a/2; no source instance is removed
--   - encoding: the actual number of probes of a possibly partial run → the extended nonnegative supremum of finite probe-history lengths; reason: it equals the source count on every terminating run, and zero-error correctness requires such termination almost surely for all roots simultaneously
--   - encoding: an arbitrary input-independent shared tape and its probabilities → an arbitrary probability space with measurable next-action equality events; reason: this is the implicit observational measurability needed for the source probabilities, without restricting the law or access to the tape
-- source:
--   Peter Kiss, Yuichi Yoshida, The Local Probe Complexity of Maximal Independent Set, STOC 2027 submission #871 (October 2026), p. 3, PDF p. 5, Theorem 1.2; proof: p. 33, PDF p. 35, Eq. (47)

import Definitions.Def_LocalProbeMIS871_Greedy_Supplement_Oracle

open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
universe uTheorem12

namespace LocalProbeMIS871.Greedy.Supplement

/-- Theorem 1.2, printed p.3 / PDF5; the probability 1/16 is supplied by Eq.(47).
All existential input data are fixed before the tape is sampled. -/
theorem theorem_1_2 :
    ∃ c : ℝ, 0 < c ∧ ∃ Δ₀ : ℕ, 2 ≤ Δ₀ ∧ ∀ Δ : ℕ, Δ₀ ≤ Δ →
      ∀ (Ω : Type uTheorem12) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (A : Algorithm Ω), ZeroError μ Δ A →
        ∃ n : ℕ, 0 < n ∧ ∃ (G : SimpleGraph (Fin n)) (L : AdjacencyLists G)
          (v : Fin n), DegreeBound G Δ ∧
            (1 / 16 : ENNReal) ≤ μ {r |
              ENNReal.ofReal (c * (Δ : ℝ) ^ (3 / 2 : ℝ)) ≤ probeCount A Δ L v r} := by sorry

end LocalProbeMIS871.Greedy.Supplement
