-- Prove2me | Theorems.Thm_OnlineRandomization_Tightness_online_competitive
-- name    : OnlineRandomization.Tightness.online_competitive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:34:19.572192+00:00
-- url     : https://prove2.me/theorems/178172cb-864a-4383-9c1b-c173c90c359a
-- title:
--   §2, pp. 12–13 — the uniform algorithm $G$ is $\alpha$-competitive against any adaptive on-line adversary in the mates game
-- statement:
--   Let $t \ge 1$ be an integer and let $m, M, \alpha$ be reals with $1 \le m \le M$,
--   $$
--   \alpha = \frac{1 + (2t-1)M}{2 + (2t-2)m}, \qquad \alpha\,(m - 1) \le M - m .
--   $$
--   In the mates game with parameters $t, m, M$, the randomized algorithm $G$ that draws its first answer $a_1$ uniformly from the $2t$ answers is $\alpha$-competitive against any adaptive on-line adversary $S$:
--   $$
--   \mathbb E_{a_1}\bigl[c_{G}(S)\bigr] \le \mathbb E_{a_1}\bigl[\alpha \, c_S(G)\bigr].
--   $$
--
--   The adversary's first answer $b_1$ is fixed before $a_1$ is drawn, so $a_1 = b_1$ and $a_1 = \bar b_1$ each have probability $\frac1{2t}$. The adversary's best reply is $r_2 = a_1$ when $a_1 = b_1$ and $r_2 = \bar a_1$ otherwise; then it pays $\frac{2 + (2t-2)m}{2t}$ in expectation and $G$ pays $\frac{1 + (2t-1)M}{2t}$, a ratio of exactly $\alpha$. This is the second half of the first bullet of the tightness claim.
--
--   **Formalization Note.** Competitiveness is with the ratio function $x \mapsto \alpha x$, applied inside the expectation as on p. 9. The hypothesis $\alpha(m-1) \le M - m$ is not on the page; it is what the "simple case analysis" needs when $a_1 \notin \{b_1, \bar b_1\}$ (otherwise the reply $r_2 = b_1$ beats $r_2 = \bar a_1$ and, for $t \ge 2$, $G$ is not $\alpha$-competitive). The page's condition $M \ge m^2$ does not imply it. The hypothesis $1 \le m \le M$ makes the page's "positive" $m, M$ explicit at the strength the case analysis uses (it gives $\alpha \ge 1$); without $m \le M$ the hypotheses admit negative $M$ and $\alpha$ (e.g. $t = 2$, $m = 10$, $M = -46$, $\alpha = -137/22$), for which the statement is false. The page prints the adversary's expected cost as $\frac{2 + (2t+2)m}{2t}$; the ratio it then states uses $\frac{2 + (2t-2)m}{2t}$, which is the correct value. The game uses the disclosed pin $f_0 = 0$, $f_1 \equiv 1$.
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript pp. 12-13, §2 ("To see that G is α-competitive against any adaptive on-line adversary ...")

import Mathlib
import Definitions.Def_OnlineRandomization_Tightness_Model
import Definitions.Def_OnlineRandomization_Tightness_MatesGame

namespace OnlineRandomization.Tightness

/-- Manuscript pp. 12–13: if `1 ≤ m ≤ M`, `α = (1 + (2t − 1)M)/(2 + (2t − 2)m)` and
`α(m − 1) ≤ M − m`, the uniform algorithm `G` is `α`-competitive (ratio `x ↦ α·x`) against
any adaptive on-line adversary in the mates game. -/
theorem online_competitive (t : ℕ) [NeZero t] (m M α : ℝ) (hm : 1 ≤ m) (hmM : m ≤ M)
    (hα : α = (1 + (2 * (t : ℝ) - 1) * M) / (2 + (2 * (t : ℝ) - 2) * m))
    (hgap : α * (m - 1) ≤ M - m) :
    IsCompetitiveOnline (matesGame t m M) (fun x => α * x) (unifAlg t) := by sorry

end OnlineRandomization.Tightness
