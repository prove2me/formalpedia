-- Prove2me | Theorems.Thm_Max3CutHard_Supplement_theorem_1_3
-- name    : Max3CutHard.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:48:32.735584+00:00
-- url     : https://prove2.me/theorems/58c8da7b-0cca-4831-87f2-5dc9a677db22
-- title:
--   Theorem 1.3 — $k$-colourable graphs: $82/85$ ($k=4$), $119/122$ ($k=5$), and $1-3/(51+34L+3\binom L2)$ for $4\le k\le20$
-- statement:
--   **Theorem 1.3.** For every $\varepsilon>0$:
--
--   1. it is NP-hard to distinguish 4-colourable graphs from graphs in which every 4-colouring cuts at most an $82/85+\varepsilon\approx0.965$ fraction of the edge weight;
--   2. it is NP-hard to distinguish 5-colourable graphs from graphs in which every 5-colouring cuts at most a $119/122+\varepsilon\approx0.975$ fraction of the edge weight;
--   3. for every $k$ with $4\le k\le20$, writing $L=k-3$, it is NP-hard to distinguish $k$-colourable graphs from graphs in which every $k$-colouring $\chi$ satisfies
--
--   $$\mathrm{cut}_\chi(G)\ \le\ \Big(1-\frac{3}{51+34L+3\binom L2}+\varepsilon\Big)\,w(G).$$
--
--   The third clause is the paper's "similar improvements hold for every $k$ from 4 to 20 (Section 6)", with the ratio computed in the proof of Theorem 1.3; at $L=1,2$ it is $82/85$ and $119/122$.
--
--   These are hardness results with perfect completeness: the YES instances are properly $k$-colourable, i.e. some $k$-colouring cuts every edge.
--
--   Differences from the source:
--   - generalization: weighted graph G with non-negative real edge weights → ℕ-weighted loopless multigraph OptInapprox.MaxCut.WMaxCut (an edge listed m times has weight m) with the unary encoding encMaxCut; reason: the hard instances are a subclass of weighted graphs and the inclusion is polynomial-time, so hardness on the subclass implies the source's claim (same convention as the published goal theorem_1_1)
--   - encoding: k-colourable graph → some χ : Fin G.n → Fin k with cutK k G χ = wt G (every listed edge bichromatic); reason: WMaxCut is loopless, so cutting every listed edge is exactly a proper k-colouring
--   - encoding: the two cases of the gap problem → both promise sets also require 0 < w(G); reason: at w(G) = 0 both cases hold, so the problem is undefined there; the clause excludes only that case
--   - reading: Similar improvements hold for every k from 4 to 20 (Section 6) → for 4 ≤ k ≤ 20, gap between k-colourable and every k-colouring cuts ≤ (1 − 3/(51 + 34L + 3·C(L,2)) + ε)·w(G), L = k − 3; reason: the sentence points to Section 6, whose proof of Theorem 1.3 (p.12) computes exactly this ratio (82/85 and 119/122 at L = 1, 2); the comparison with earlier bounds is not a mathematical claim
--   - encoding: colours [k], vertices V → Fin k, Fin G.n; reason: Lean convention; same instances
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Theorem 1.3, p.1; ratio from the Proof of Theorem 1.3, p.12

import Mathlib
import Definitions.Def_SetCoverThreshold_SetCover_Complexity
import Definitions.Def_OptInapprox_MaxCut_UGC
import Definitions.Def_Max3CutHard_cutK
import Definitions.Def_Max3CutHard_wt
open OptInapprox.MaxCut

namespace Max3CutHard.Supplement

open Max3CutHard

/-- **Theorem 1.3.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Theorem 1.3, p.1: "For every `ε > 0` it is NP-hard to
distinguish 4-colourable graphs from graphs in which every 4-colouring cuts at most an
`82/85 + ε ≈ 0.965` fraction of the edge weight, and 5-colourable graphs from graphs in which
every 5-colouring cuts at most a `119/122 + ε ≈ 0.975` fraction. Similar improvements hold for
every `k` from 4 to 20 (Section 6)." The general ratio is the one computed in the Proof of
Theorem 1.3, p.12: "the ratio is `1 − Δs/m_L = 1 − 3/(51 + 34L + 3 (L choose 2))`, e.g. `82/85`
for `L = 1` and `119/122` for `L = 2`. Perfect completeness is preserved."

**Formalization Note.** Graphs are the published ℕ-weighted loopless multigraphs `WMaxCut` with
the unary encoding `encMaxCut`; NP-hardness of distinguishing is the published Karp-style
`GapNPHard`. A graph is `k`-colourable iff some `χ : Fin G.n → Fin k` cuts every listed edge
(`cutK k G χ = wt G`). Both promise sets require `0 < w(G)` (at `w(G) = 0` the two cases
coincide). The third clause is the "every `k` from 4 to 20" sentence with `L = k − 3`.
Unconditional: the 16/17 hardness of 3-colourable graphs of [AOTW14], used in the proof, is not a
hypothesis. -/
theorem theorem_1_3 :
    (∀ ε : ℝ, 0 < ε →
      SetCoverThreshold.SetCover.GapNPHard encMaxCut
        (fun G => 0 < wt G ∧ ∃ χ : Fin G.n → Fin 4, cutK 4 G χ = wt G)
        (fun G => 0 < wt G ∧ ∀ χ : Fin G.n → Fin 4,
          (cutK 4 G χ : ℝ) ≤ (82 / 85 + ε) * (wt G : ℝ))) ∧
    (∀ ε : ℝ, 0 < ε →
      SetCoverThreshold.SetCover.GapNPHard encMaxCut
        (fun G => 0 < wt G ∧ ∃ χ : Fin G.n → Fin 5, cutK 5 G χ = wt G)
        (fun G => 0 < wt G ∧ ∀ χ : Fin G.n → Fin 5,
          (cutK 5 G χ : ℝ) ≤ (119 / 122 + ε) * (wt G : ℝ))) ∧
    (∀ k : ℕ, 4 ≤ k → k ≤ 20 → ∀ ε : ℝ, 0 < ε →
      SetCoverThreshold.SetCover.GapNPHard encMaxCut
        (fun G => 0 < wt G ∧ ∃ χ : Fin G.n → Fin k, cutK k G χ = wt G)
        (fun G => 0 < wt G ∧ ∀ χ : Fin G.n → Fin k,
          (cutK k G χ : ℝ) ≤
            (1 - 3 / (51 + 34 * ((k - 3 : ℕ) : ℝ) + 3 * ((k - 3).choose 2 : ℝ)) + ε) *
              (wt G : ℝ))) := by sorry

end Max3CutHard.Supplement
