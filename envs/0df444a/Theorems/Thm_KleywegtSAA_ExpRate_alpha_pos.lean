-- Prove2me | Theorems.Thm_KleywegtSAA_ExpRate_alpha_pos
-- name    : KleywegtSAA.ExpRate.alpha_pos
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:04:06.88513+00:00
-- url     : https://prove2.me/theorems/7ddbf124-0993-4d41-a880-8e97f06a6dd1
-- title:
--   §2.1, (2.3), p. 3 — α(ε) = min_{x∈𝒮∖𝒮^ε} g(x) − v* − ε > 0
-- statement:
--   Let $\mathcal S$ be a nonempty finite set, $g : \mathcal S \to \mathbb R$ any function, $v^* = \min_{\mathcal S} g$, and $\varepsilon \ge 0$. Let $\mathcal S^\varepsilon = \{x \in \mathcal S : g(x) \le v^* + \varepsilon\}$ and suppose $\mathcal S \setminus \mathcal S^\varepsilon$ is nonempty. Then
--   $$\alpha(\varepsilon) = \min_{x \in \mathcal S \setminus \mathcal S^\varepsilon} g(x) - v^* - \varepsilon > 0.$$
--
--   The number $\alpha(\varepsilon)$ measures how well the $\varepsilon$-optimal solutions are separated from the rest; it is the margin that the sample average must resolve.
--
--   **Formalization Note** The statement holds for any real function on $\mathcal S$, so it is stated without probability. When $\mathcal S^\varepsilon = \mathcal S$ the paper's $\alpha(\varepsilon)$ is a minimum over the empty set and is undefined; the nonemptiness of $\mathcal S \setminus \mathcal S^\varepsilon$ is therefore a hypothesis.
-- source:
--   Kleywegt & Shapiro, The sample average approximation method for stochastic discrete optimization, preprint (two-author version, sha256 56657748…), p. 3, (2.3) and the sentence after it

import Mathlib
import Definitions.Def_KleywegtSAA_ExpRate_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace KleywegtSAA.ExpRate

/-- (2.3), p. 3: for `ε ≥ 0`, if `S \ S^ε` is nonempty then
`α(ε) = min_{x ∈ S \ S^ε} g(x) − v* − ε > 0`. Stated for an arbitrary real function `g` on `S`. -/
theorem alpha_pos {X : Type*} (S : Finset X) (hS : S.Nonempty) (g : X → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε) (hne : (nonOptSet S hS g ε).Nonempty) :
    0 < alpha S hS g ε hne := by sorry

end KleywegtSAA.ExpRate
