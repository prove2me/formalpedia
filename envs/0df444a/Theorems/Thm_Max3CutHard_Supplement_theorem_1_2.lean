-- Prove2me | Theorems.Thm_Max3CutHard_Supplement_theorem_1_2
-- name    : Max3CutHard.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:48:06.421565+00:00
-- url     : https://prove2.me/theorems/4fc3f788-4313-4517-90d0-8e0b7cc24cda
-- title:
--   Theorem 1.2 — Max-$k$-Cut is NP-hard to approximate within $1-2/\Gamma_{k-3}+\varepsilon$ ($45/47$ for $k=4$, $33/34$ for $k=5$)
-- statement:
--   **Theorem 1.2.** For every $k\ge3$ and $\varepsilon>0$, Max-$k$-Cut is NP-hard to approximate within
--
--   $$1-\frac{2}{\Gamma_{k-3}}+\varepsilon,\qquad \Gamma_L=29+18L+3\binom L2 .$$
--
--   In particular, Max-4-Cut is NP-hard to approximate within $45/47+\varepsilon\approx0.957$, and Max-5-Cut within $33/34+\varepsilon\approx0.971$.
--
--   Here "NP-hard to approximate within $r$" means that for some $c>0$ and $s$ with $s/c\le r$ it is NP-hard to distinguish weighted graphs $G$ with $\max_\chi\mathrm{cut}_\chi(G)\ge c\,w(G)$ from those with $\max_\chi\mathrm{cut}_\chi(G)\le s\,w(G)$, the maximum running over $k$-colourings $\chi$.
--
--   For $k=3$ the bound is the $27/29$ of Theorem 1.1; for every $k$ from $3$ to $20$ these bounds (with Theorem 1.3) are the best known NP-hardness results for Max-$k$-Cut.
--
--   Differences from the source:
--   - generalization: weighted graph G with non-negative real edge weights → ℕ-weighted loopless multigraph OptInapprox.MaxCut.WMaxCut (an edge listed m times has weight m) with the unary encoding encMaxCut; reason: the hard instances are a subclass of weighted graphs and the inclusion is polynomial-time, so hardness on the subclass implies the source's claim (same convention as the published goal theorem_1_1)
--   - encoding: the two cases of the gap problem → both promise sets also require 0 < w(G); reason: at w(G) = 0 both cases hold, so the problem is undefined there; the clause excludes only that case
--   - reading: Max-k-Cut is NP-hard to approximate within r → ∃ c > 0, s with s/c ≤ r and MaxKCutHard k c s; reason: Section 2 defines (c, s)-hardness and states that it implies NP-hardness of approximation within s/c; the published goal uses the same reading
--   - encoding: colours [k], vertices V → Fin k, Fin G.n; reason: Lean convention; same instances
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Theorem 1.2, p.1

import Mathlib
import Definitions.Def_Max3CutHard_MaxKCutHard
import Definitions.Def_Max3CutHard_Supplement_Gamma

namespace Max3CutHard.Supplement

open Max3CutHard

/-- **Theorem 1.2.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Theorem 1.2, p.1: "For every `k ≥ 3` and `ε > 0`,
Max-k-Cut is NP-hard to approximate within `1 − 2/Γ_{k−3} + ε`, where
`Γ_L = 29 + 18L + 3 (L choose 2)`. In particular, Max-4-Cut is NP-hard to approximate within
`45/47 + ε ≈ 0.957`, and Max-5-Cut within `33/34 + ε ≈ 0.971`."

**Formalization Note.** "NP-hard to approximate within `r`" is read through Section 2's
definition, exactly as in the published goal `Max3CutHard.theorem_1_1`: Max-`k`-Cut is
`(c, s)`-hard (the published `MaxKCutHard k c s`, over ℕ-weighted loopless multigraphs with
`0 < w(G)` in both promise sets) for some `c > 0` and `s` with `s/c ≤ r`. `Γ_{k−3}` uses
natural-number subtraction, which is exact since `3 ≤ k`. Unconditional: Håstad's Theorem 2.1 is
not a hypothesis. -/
theorem theorem_1_2 :
    (∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε →
      ∃ c s : ℝ, 0 < c ∧ s / c ≤ 1 - 2 / (Gamma (k - 3) : ℝ) + ε ∧ MaxKCutHard k c s) ∧
    (∀ ε : ℝ, 0 < ε → ∃ c s : ℝ, 0 < c ∧ s / c ≤ 45 / 47 + ε ∧ MaxKCutHard 4 c s) ∧
    (∀ ε : ℝ, 0 < ε → ∃ c s : ℝ, 0 < c ∧ s / c ≤ 33 / 34 + ε ∧ MaxKCutHard 5 c s) := by sorry

end Max3CutHard.Supplement
