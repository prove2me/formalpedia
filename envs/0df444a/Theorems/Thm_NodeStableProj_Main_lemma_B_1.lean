-- Prove2me | Theorems.Thm_NodeStableProj_Main_lemma_B_1
-- name    : NodeStableProj.Main.lemma_B_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:59:57.137957+00:00
-- url     : https://prove2.me/theorems/afe828b9-d16d-43a6-908e-24e7af67156b
-- title:
--   Lemma B.1 — Algorithm 5 has the output law of Algorithm 1 and runs in O(n + m) on sorted edges, O(n + m log m) in general
-- statement:
--   Let $G=(V,E)$ be an $n$-vertex graph with $V=[n]=\{1,\dots,n\}$ and $m$ edges.
--   1. For integers $0<D<\hat D$ and $\tilde\varepsilon>0$, if both algorithms use the same rule to select a maximal $\hat D$-bounded subgraph in the fallback step, the output distribution of Algorithm 5 on $G$ is identical to that of Algorithm 1 on $G$.
--   2. If the edges of $G$ are given in lexicographic order, Algorithm 5 runs in time $O(n+m)$: there are a program on the machine and a constant $C$ such that on every such encoding the program's output law is that of Algorithm 5 (for some fallback rule) and every run halts within $C(n+m)$ steps. In general, Algorithm 5 can be implemented in time $O(n+m\log m)$: there are a program and a constant $C$ such that on every encoding the output law is that of Algorithm 5 (for some fallback rule) and every run halts within $C(n+m\log m)$ steps. The bounds are asymptotic, for $n,m\ge2$.
--
--   The fast-forwarded implementation is what gives the near-linear running time of Lemma 3.3 and Theorem 3.5.
--
--   Differences from the source:
--   - reading: "runs in time O(n + m)" / "can be implemented in time O(n + m log m)" → ∃ program (law of Algorithm 5 for some fallback rule) and C with every run halting within C(n + m), resp. C(n + m log m), steps, for n, m ≥ 2; reason: §2 convention for asymptotic bounds; the machine reading of "time"
--   - reading: "any maximal D̂-bounded subgraph" in the implemented fallback → the program's fallback rule is chosen by the program (existentially), per input encoding; reason: Algorithm 5 may return any maximal subgraph
--   - encoding: "the edges of G are given in lexicographic order" → the edge list is lexEdges G (pairs (u, v), u < v, lexicographic); the vertex list in any order; reason: the input format of Algorithm 5
-- source:
--   Aden-Ali, Sealfon, Smith, Steinke, Ullman, Node Differential Privacy via Node-Stable Graph Projections, STOC 2027 submission (manuscript sha256 42f18565…), pp. 30, 32, Lemma B.1

import Mathlib
import Definitions.Def_NodeStableProj_Main_Projection
import Definitions.Def_NodeStableProj_Main_FastForward
import Definitions.Def_NodeStableProj_Main_Machine

open MeasureTheory

namespace NodeStableProj.Main

/-- Lemma B.1, p. 32: for an `n`-vertex graph `G` on `[n]` with `m` edges,
(1) for `0 < D < D̂`, `ε̃ > 0` and any common fallback rule, Algorithm 5 and Algorithm 1 have the
same output law;
(2) a program implementing Algorithm 5 runs in `O(n + m)` steps when the edges are given in
lexicographic order, and Algorithm 5 can be implemented in `O(n + m log m)` steps in general
(asymptotic bounds for `n, m ≥ 2`). -/
theorem lemma_B_1 :
    (∀ (n : ℕ) (G : Graph) (D Dhat : ℕ) (εt : ℝ) (F : Graph → Graph),
      G.V = Finset.Icc 1 n → 0 < D → D < Dhat → 0 < εt → IsFallbackRule Dhat F →
      alg5Law D Dhat εt F G = alg1Law D Dhat εt F G) ∧
    (∃ P : Program, Admissible P ∧
      (∀ (n : ℕ) (G : Graph) (D Dhat : ℕ) (εt : ℝ) (vs : List ℕ),
        G.V = Finset.Icc 1 n → 0 < D → D < Dhat → 0 < εt → IsEncoding G vs (lexEdges G) →
        ∃ F : Graph → Graph, IsFallbackRule Dhat F ∧
          projectionProgramLaw P D Dhat εt vs (lexEdges G) =
            (alg5Law D Dhat εt F G).map edgeOutput) ∧
      ∃ C : ℝ, ∀ (n : ℕ) (G : Graph) (D Dhat : ℕ) (εt : ℝ) (vs : List ℕ),
        G.V = Finset.Icc 1 n → 0 < D → D < Dhat → 0 < εt → IsEncoding G vs (lexEdges G) →
        2 ≤ n → 2 ≤ G.E.card →
        HaltsWithin P (projectionInit D Dhat εt vs (lexEdges G)) (C * (n + G.E.card))) ∧
    (∃ P : Program, Admissible P ∧
      (∀ (n : ℕ) (G : Graph) (D Dhat : ℕ) (εt : ℝ) (vs : List ℕ) (es : List (ℕ × ℕ)),
        G.V = Finset.Icc 1 n → 0 < D → D < Dhat → 0 < εt → IsEncoding G vs es →
        ∃ F : Graph → Graph, IsFallbackRule Dhat F ∧
          projectionProgramLaw P D Dhat εt vs es =
            (alg5Law D Dhat εt F G).map edgeOutput) ∧
      ∃ C : ℝ, ∀ (n : ℕ) (G : Graph) (D Dhat : ℕ) (εt : ℝ) (vs : List ℕ) (es : List (ℕ × ℕ)),
        G.V = Finset.Icc 1 n → 0 < D → D < Dhat → 0 < εt → IsEncoding G vs es →
        2 ≤ n → 2 ≤ G.E.card →
        HaltsWithin P (projectionInit D Dhat εt vs es)
          (C * (n + G.E.card * Real.log G.E.card))) := by sorry

end NodeStableProj.Main
