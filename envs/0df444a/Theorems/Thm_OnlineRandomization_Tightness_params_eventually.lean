-- Prove2me | Theorems.Thm_OnlineRandomization_Tightness_params_eventually
-- name    : OnlineRandomization.Tightness.params_eventually
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T07:33:46.573027+00:00
-- url     : https://prove2.me/theorems/6ab08a0c-2144-45cd-8e56-74a1a40368b8
-- title:
--   §2, p. 12 — for all large $t$, $M(t) \ge \max(m(t)^2, C)$, $1 \le m(t) \le M(t)$ and $\alpha(m(t)-1) \le M(t) - m(t)$
-- statement:
--   Let $1 < \beta \le \alpha$ and $C < \alpha\beta$, and let $m(t)$, $M(t)$ be the solutions of the equations $\beta = \frac{(2t-2)m + M + 1}{2t}$, $\alpha = \frac{1 + (2t-1)M}{2 + (2t-2)m}$:
--   $$
--   m(t) = \frac{1 + (2t-1)(2t\beta - 1) - 2\alpha}{(2t-2)(\alpha + 2t - 1)}, \qquad M(t) = \frac{2t\alpha\beta + \alpha - 1}{\alpha + 2t - 1}.
--   $$
--   Then for every sufficiently large integer $t$:
--
--   1. $M(t) \ge \max(m(t)^2, C)$;
--   2. $1 \le m(t) \le M(t)$;
--   3. $\alpha\,(m(t) - 1) \le M(t) - m(t)$.
--
--   Item 1 is the paper's condition on $t$. Items 2 and 3 are what the two case analyses of p. 12 use: $m, M \ge 1$ makes the oblivious adversary's cost at least $1$, and item 3 makes "set $r_2$ to the mate of $a_1$" the adaptive on-line adversary's best reply when $a_1$ is neither $b_1$ nor its mate.
--
--   **Formalization Note.** The page states the range $1 \le \beta \le \alpha$; this statement takes $1 < \beta$. At $\beta = 1 < \alpha$ the solution has $m(t) < 1$ for every $t$, so item 2 fails and the construction does not give a $\beta$-competitive $G$. Items 2 and 3 are not on the page; the page's condition $M \ge m^2$ does not imply item 3 (e.g. $m = 2$, $M = 4$, $t \ge 2$ gives $\alpha > 2$).
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript p. 12, §2, first paragraph ("The parameter t is chosen sufficiently large that M ≥ max(m², C)")

import Mathlib
import Definitions.Def_OnlineRandomization_Tightness_Model
import Definitions.Def_OnlineRandomization_Tightness_MatesGame

namespace OnlineRandomization.Tightness

open Filter

/-- Manuscript p. 12, first paragraph: for `1 < β ≤ α` and `C < αβ`, every sufficiently large
`t` gives `M(t) ≥ max(m(t)², C)` (the page's condition), together with `1 ≤ m(t) ≤ M(t)` and
`α(m(t) − 1) ≤ M(t) − m(t)`, which the case analyses of p. 12 use. -/
theorem params_eventually (α β C : ℝ) (hβ : 1 < β) (hβα : β ≤ α) (hC : C < α * β) :
    ∀ᶠ t : ℕ in atTop,
      max (paramSmall α β t ^ 2) C ≤ paramLarge α β t ∧
      1 ≤ paramSmall α β t ∧
      paramSmall α β t ≤ paramLarge α β t ∧
      α * (paramSmall α β t - 1) ≤ paramLarge α β t - paramSmall α β t := by sorry

end OnlineRandomization.Tightness
