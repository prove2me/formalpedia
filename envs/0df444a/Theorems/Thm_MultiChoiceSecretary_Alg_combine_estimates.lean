-- Prove2me | Theorems.Thm_MultiChoiceSecretary_Alg_combine_estimates
-- name    : MultiChoiceSecretary.Alg.combine_estimates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:37:23.599605+00:00
-- url     : https://prove2.me/theorems/965efd86-0d15-4b5d-9e75-553c692a174f
-- title:
--   Proof sketch of Theorem 2.1, PDF p. 2 — the easy computation: (1 − 5/√(k/2))(1 − 1/(2√k))/2 + (1/2 − √(1/k)) > 1 − 5/√k
-- statement:
--   For every real $k > 0$,
--
--   $$1 - \frac{5}{\sqrt k} \;<\; \Big(1 - \frac{5}{\sqrt{k/2}}\Big)\Big(1 - \frac{1}{2\sqrt k}\Big)\frac12 + \Big(\frac12 - \sqrt{\frac1k}\Big).$$
--
--   The two terms on the right are the estimates, in units of $v$, of the modified value selected among the first $m$ arrivals (by the induction hypothesis) and after them. This is the "easy computation" that closes the induction step of Theorem 2.1.
--
--   **Formalization Note.** Stated for every real $k > 0$, which contains every integer $k \ge 1$.
-- source:
--   Kleinberg, A multiple-choice secretary algorithm with applications to online auctions, SODA 2005, PDF p. 2 (right column), proof sketch of Theorem 2.1, "Combining the estimates from the preceding two paragraphs, an easy computation verifies …"

import Mathlib
import Definitions.Def_MultiChoiceSecretary_Alg_Setting

namespace MultiChoiceSecretary.Alg

theorem combine_estimates (k : ℝ) (hk : 0 < k) :
    1 - 5 / Real.sqrt k <
      (1 - 5 / Real.sqrt (k / 2)) * (1 - 1 / (2 * Real.sqrt k)) * (1 / 2) +
        (1 / 2 - Real.sqrt (1 / k)) := by sorry

end MultiChoiceSecretary.Alg
