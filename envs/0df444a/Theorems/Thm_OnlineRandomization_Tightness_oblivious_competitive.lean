-- Prove2me | Theorems.Thm_OnlineRandomization_Tightness_oblivious_competitive
-- name    : OnlineRandomization.Tightness.oblivious_competitive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:34:10.689989+00:00
-- url     : https://prove2.me/theorems/892b0535-db0c-49be-8c97-652659c7936f
-- title:
--   §2, p. 12 — the uniform algorithm $G$ is $\beta$-competitive against any oblivious adversary in the mates game
-- statement:
--   Let $t \ge 1$ be an integer and let $m, M \ge 1$. In the mates game with parameters $t, m, M$, let $G$ be the randomized algorithm that draws its first answer $a_1$ uniformly from the $2t$ answers, and put
--   $$
--   \beta = \frac{(2t-2)m + M + 1}{2t}.
--   $$
--   Then $G$ is $\beta$-competitive against any oblivious adversary: for every request sequence $\underline r$,
--   $$
--   \mathbb E_{a_1}\bigl[f_n(\underline r, G(\underline r))\bigr] \le \beta \cdot c(\underline r),
--   $$
--   where $c(\underline r)$ is the off-line optimum.
--
--   For $n \ge 2$, whatever $r_2$ is, $G$ pays $1$ with probability $\frac1{2t}$, $M$ with probability $\frac1{2t}$ and $m$ with probability $\frac{2t-2}{2t}$, so its expected cost is $\beta$, while the optimum is $1$. This is the first half of the first bullet of the tightness claim.
--
--   **Formalization Note.** Competitiveness is with the ratio function $x \mapsto \beta x$ (no additive constant). The hypotheses $m, M \ge 1$ are what the page's "the oblivious adversary's cost is at least 1" needs. The game uses the disclosed pin $f_0 = 0$, $f_1 \equiv 1$; the case $n = 1$ then needs $\beta \ge 1$, which follows from $m, M \ge 1$. The page prints the probability of cost $m$ as $\frac{2t-2}{t}$; the expected cost it then computes uses $\frac{2t-2}{2t}$, which is the correct value.
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript p. 12, §2 ("To see that G is β-competitive against any oblivious adversary ...")

import Mathlib
import Definitions.Def_OnlineRandomization_Tightness_Model
import Definitions.Def_OnlineRandomization_Tightness_MatesGame

namespace OnlineRandomization.Tightness

/-- Manuscript p. 12: if `m, M ≥ 1` and `β = ((2t − 2)m + M + 1)/(2t)`, the uniform algorithm
`G` is `β`-competitive (ratio `x ↦ β·x`) against any oblivious adversary in the mates game. -/
theorem oblivious_competitive (t : ℕ) [NeZero t] (m M β : ℝ) (hm : 1 ≤ m) (hM : 1 ≤ M)
    (hβ : β = ((2 * (t : ℝ) - 2) * m + M + 1) / (2 * (t : ℝ))) :
    IsCompetitiveObl (matesGame t m M) (fun x => β * x) (unifAlg t) := by sorry

end OnlineRandomization.Tightness
