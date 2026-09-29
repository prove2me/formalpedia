-- Prove2me | Theorems.Thm_KLZ97_threshold_theorem
-- name    : KLZ97.threshold_theorem
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T18:24:35.916997+00:00
-- url     : https://prove2.me/theorems/b55be58f-767d-4165-add2-848f0f682658
-- title:
--   Threshold theorem: accuracy below threshold at polylogarithmic overhead
-- statement:
--   The paper's main result, in the quantitative form its analysis establishes. Let $f \ge 1$ be the number of minimal pairs of error locations that can make an encoded gate fail, and let $K \ge 2$ bound the resources one encoded gate consumes at the level below. If the physical failure parameter $p$ lies below the threshold $1/f$, then for every computation of $n$ gates and every target failure probability $q$ with $0 < q < n$ there is a number $h$ of concatenation levels such that
--   $$n E_h < q,$$
--   so the computation fails with probability less than $q$, while the resource overhead per computational gate satisfies
--   $$K^{h} \le K^{2} \left( \max\left(1, \frac{\log(n/q)}{\log(1/(fp))} \right) \right)^{\log_2 K},$$
--   which is polylogarithmic in $n$ and $1/q$. The threshold is not a hard-coded number: it is the hypothesis $p < 1/f$, so the statement is unaffected by improvements to the paper's estimates $f \le 337195$ and the corresponding numerical thresholds $3.0 \times 10^{-6}$ and $1.3 \times 10^{-6}$.
-- source:
--   Knill, Laflamme, Zurek, Resilient Quantum Computation: Error Models and Thresholds, arXiv:quant-ph/9702058v1, https://arxiv.org/abs/quant-ph/9702058, Sections I.F, II.C and II.F, pp. 6, 8-9 (threshold and overhead statements)

import Mathlib
import Definitions.Def_KLZ97_model

namespace KLZ97

theorem threshold_theorem (f K p q : ℝ) (n : ℕ) (hf : 1 ≤ f) (hK : 2 ≤ K) (hp : 0 ≤ p)
    (hthreshold : p < 1 / f) (hq : 0 < q) (hqn : q < n) :
    ∃ h : ℕ, (n : ℝ) * levelError f p h < q ∧
      K ^ h ≤ K ^ 2 *
        (max 1 (Real.log ((n : ℝ) / q) / Real.log (1 / (f * p)))) ^ Real.logb 2 K := by
  sorry

end KLZ97
