-- Prove2me | Theorems.Thm_Max3CutHard_theorem_1_1
-- name    : Max3CutHard.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:47:13.313042+00:00
-- url     : https://prove2.me/theorems/333daa45-4051-44c6-aea0-db30eea38a53
-- title:
--   Theorem 1.1 — Max-3-Cut: gap $29/30-\varepsilon$ vs. $9/10+\varepsilon$, hard within $27/29+\varepsilon$
-- statement:
--   **Theorem 1.1.** For every $\varepsilon>0$ it is NP-hard, given a weighted graph $G$, to distinguish between the case that some 3-colouring cuts at least a $(29/30-\varepsilon)$ fraction of the total edge weight,
--
--   $$\exists\chi:\ \mathrm{cut}_\chi(G)\ \ge\ \Big(\frac{29}{30}-\varepsilon\Big)w(G),$$
--
--   and the case that every 3-colouring cuts at most a $(9/10+\varepsilon)$ fraction,
--
--   $$\forall\chi:\ \mathrm{cut}_\chi(G)\ \le\ \Big(\frac9{10}+\varepsilon\Big)w(G).$$
--
--   In particular, Max-3-Cut is NP-hard to approximate within $27/29+\varepsilon\approx0.931$: for every $\varepsilon>0$ there are $c>0$ and $s$ with $s/c\le 27/29+\varepsilon$ such that Max-3-Cut is $(c,s)$-hard.
--
--   This improves the previous NP-hardness bound $16/17$ of Austrin, O'Donnell, Tan and Wright for Max-3-Cut.
--
--   Differences from the source:
--   - generalization: weighted graph G with non-negative real edge weights → ℕ-weighted loopless multigraph OptInapprox.MaxCut.WMaxCut (an edge listed m times has weight m) with the unary encoding encMaxCut; reason: the hard instances are a subclass of weighted graphs and the inclusion is polynomial-time, so hardness on the subclass implies the source's claim; the source itself claims hardness for unweighted simple graphs (p.4)
--   - encoding: the two cases of the gap problem → both promise sets also require 0 < w(G); reason: at w(G) = 0 both cases hold, so the problem is undefined there; the clause excludes only that case
--   - reading: it is NP-hard to distinguish; NP-hard to approximate within 27/29 + ε → SetCoverThreshold.SetCover.GapNPHard; ∃ c > 0, s with s/c ≤ 27/29 + ε and MaxKCutHard 3 c s; reason: Section 2 defines (c, s)-hardness and states that it implies NP-hardness of approximation within s/c
--   - encoding: colours [3], vertices V → Fin 3, Fin G.n; reason: Lean convention; same instances
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Theorem 1.1, p.1

import Mathlib
import Definitions.Def_SetCoverThreshold_SetCover_Complexity
import Definitions.Def_OptInapprox_MaxCut_UGC
import Definitions.Def_Max3CutHard_cutK
import Definitions.Def_Max3CutHard_wt
import Definitions.Def_Max3CutHard_MaxKCutHard
open OptInapprox.MaxCut

namespace Max3CutHard

/-- **Theorem 1.1.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Theorem 1.1, p.1: "For every `ε > 0` it is NP-hard, given a weighted
graph `G`, to distinguish between the case that some 3-colouring cuts at least a `(29/30 − ε)`
fraction of the total edge weight and the case that every 3-colouring cuts at most a
`(9/10 + ε)` fraction. In particular, Max-3-Cut is NP-hard to approximate within
`27/29 + ε ≈ 0.931`."

**Formalization Note.** Graphs are the published ℕ-weighted loopless multigraphs `WMaxCut` with
the published unary encoding `encMaxCut` (a subclass of non-negatively weighted graphs, so the
hardness is stronger); both promise sets require `0 < w(G)`. NP-hardness is the published
Karp-style `GapNPHard`. "NP-hard to approximate within `27/29 + ε`" is read through Section 2's
definition: Max-3-Cut is `(c, s)`-hard (`MaxKCutHard 3 c s`) for some `c > 0` with
`s/c ≤ 27/29 + ε`. Unconditional: Håstad's Theorem 2.1 is not a hypothesis. -/
theorem theorem_1_1 :
    (∀ ε : ℝ, 0 < ε →
      SetCoverThreshold.SetCover.GapNPHard encMaxCut
        (fun G => 0 < wt G ∧ ∃ χ : Fin G.n → Fin 3, (29 / 30 - ε) * (wt G : ℝ) ≤ (cutK 3 G χ : ℝ))
        (fun G => 0 < wt G ∧ ∀ χ : Fin G.n → Fin 3, (cutK 3 G χ : ℝ) ≤ (9 / 10 + ε) * (wt G : ℝ))) ∧
    (∀ ε : ℝ, 0 < ε → ∃ c s : ℝ, 0 < c ∧ s / c ≤ 27 / 29 + ε ∧ MaxKCutHard 3 c s) := by sorry

end Max3CutHard
