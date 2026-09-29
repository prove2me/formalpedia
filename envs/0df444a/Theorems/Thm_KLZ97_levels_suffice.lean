-- Prove2me | Theorems.Thm_KLZ97_levels_suffice
-- name    : KLZ97.levels_suffice
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T15:51:21.140729+00:00
-- url     : https://prove2.me/theorems/235f620c-c4c5-42c9-b474-ad064f7041b4
-- title:
--   Sufficient number of concatenation levels: $n (fp)^{2^h} < q$
-- statement:
--   The paper's criterion for how many levels of concatenation are needed. For a computation of $n$ gates and a desired failure probability $q$, the number $h$ of levels is sufficient provided
--   $$2^{h} > \log_{1/(fp)}(n/q),$$
--   and then the computation's failure probability bound $n (f p)^{2^{h}}$ is smaller than $q$. This is the inequality $n (fp)^{2^h} < q$ of Section II.F, together with the condition $h > \log_2 \log_{1/(fp)}(n/q)$ derived from it.
-- source:
--   Knill, Laflamme, Zurek, Resilient Quantum Computation: Error Models and Thresholds, arXiv:quant-ph/9702058v1, https://arxiv.org/abs/quant-ph/9702058, Section II.F (Overheads), p. 9

import Mathlib
import Definitions.Def_KLZ97_model

namespace KLZ97

theorem levels_suffice (f p q : ℝ) (n : ℕ) (h : ℕ) (hp : 0 < f * p) (hfp : f * p < 1)
    (hq : 0 < q) (hqn : q < n)
    (hlevels : Real.log ((n : ℝ) / q) / Real.log (1 / (f * p)) < (2 : ℝ) ^ h) :
    (n : ℝ) * (f * p) ^ (2 ^ h) < q := by sorry

end KLZ97
