-- Prove2me | Theorems.Thm_NodeStableProj_Main_lemma_3_3_efficiency
-- name    : NodeStableProj.Main.lemma_3_3_efficiency
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:59:27.77752+00:00
-- url     : https://prove2.me/theorems/be7e89c0-97c6-44bd-8a33-1f12ecc46add
-- title:
--   Lemma 3.3 item 2 — P_{D,D̂,ε̃} can be implemented in time O(m log m)
-- statement:
--   There is a program on the machine that implements $\mathcal P_{D,\hat D,\tilde\varepsilon}$: on every encoded input graph $G$ and all integers $0<D<\hat D$ and $\tilde\varepsilon>0$, its output law equals the output law of Algorithm 1 for some fallback rule. Moreover, for every $c'>0$ there is a constant $C$ such that on every input with $n\ge2$ vertices and $m\ge2$ edges, $n\le c'm$, every run halts within
--   $$C\,m\log m$$
--   steps.
--
--   Differences from the source:
--   - reading: "can be implemented in time O(m log m) on inputs with n vertices and m edges" → ∃ program with Algorithm 1's output law on every input and, for every c' > 0, ∃ C: n, m ≥ 2 and n ≤ c'm imply every run halts within C m log m steps; reason: §2: asymptotic bounds assume n, m ≥ 2, and running times are simplified with n = O(m) (Lemma B.1 gives O(n + m log m))
--   - reading: "any maximal D̂-bounded subgraph" in the implementation → the program's fallback rule is existential, per input encoding; reason: the algorithm may return any maximal subgraph
-- source:
--   Aden-Ali, Sealfon, Smith, Steinke, Ullman, Node Differential Privacy via Node-Stable Graph Projections, STOC 2027 submission (manuscript sha256 42f18565…), p. 11, Lemma 3.3 item 2

import Mathlib
import Definitions.Def_NodeStableProj_Main_Projection
import Definitions.Def_NodeStableProj_Main_Machine

open MeasureTheory

namespace NodeStableProj.Main

/-- Lemma 3.3, item 2 (Efficiency), p. 11: `P_{D,D̂,ε̃}` can be implemented in time
`O(m log m)` on inputs with `n` vertices and `m` edges: one program whose output law on every
encoded input equals Algorithm 1's (for a fallback rule of its choosing), and which halts on
every run within `C m log m` steps when `m ≥ 2`, `n ≥ 2` and `n ≤ c' m`. -/
theorem lemma_3_3_efficiency :
    ∃ P : Program, Admissible P ∧
      (∀ (G : Graph) (D Dhat : ℕ) (εt : ℝ) (vs : List ℕ) (es : List (ℕ × ℕ)),
        0 < D → D < Dhat → 0 < εt → IsEncoding G vs es →
        ∃ F : Graph → Graph, IsFallbackRule Dhat F ∧
          projectionProgramLaw P D Dhat εt vs es =
            (alg1Law D Dhat εt F G).map edgeOutput) ∧
      ∀ c' : ℝ, 0 < c' → ∃ C : ℝ, ∀ (G : Graph) (D Dhat : ℕ) (εt : ℝ) (vs : List ℕ)
        (es : List (ℕ × ℕ)),
        0 < D → D < Dhat → 0 < εt → IsEncoding G vs es →
        2 ≤ G.V.card → 2 ≤ G.E.card → (G.V.card : ℝ) ≤ c' * G.E.card →
        HaltsWithin P (projectionInit D Dhat εt vs es)
          (C * G.E.card * Real.log G.E.card) := by sorry

end NodeStableProj.Main
