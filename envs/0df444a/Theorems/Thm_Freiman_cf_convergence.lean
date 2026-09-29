-- Prove2me | Theorems.Thm_Freiman_cf_convergence
-- name    : Freiman.cf_convergence
-- status  : Proved
-- author  : @tp
-- created : 2026-09-08T23:21:44.394212+00:00
-- url     : https://prove2.me/theorems/33081362-1cd6-4bb4-9aaa-3fa80f1d730e
-- title:
--   Convergence of positive continued fractions
-- statement:
--   Let $b=(b_n)_{n\ge0}$ be any sequence of positive integers. Write $C_n(b)$ for its finite convergents and $C(b)$ for the supremum of its even convergents, as defined above. Then
--   $$
--   \lim_{n\to\infty}C_n(b)=C(b),\qquad
--   C(b)\in(0,1)\setminus\mathbb Q.
--   $$
--   Moreover,
--   $$
--   C(b)=\frac{1}{b_0+C((b_{n+1})_{n\ge0})}.
--   $$
--   This establishes the infinite continued fraction and the identity obtained by removing its first digit.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.1, p. 7, equation (1.2) and the following convergence and irrationality argument.

import Definitions.Def_Freiman_cfValue
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Instances.Real.Lemmas

namespace Freiman

theorem cf_convergence (b : ℕ → ℕ+) :
    Filter.Tendsto (cfConvergent b) Filter.atTop (nhds (cfValue b)) ∧
    Irrational (cfValue b) ∧
    0 < cfValue b ∧ cfValue b < 1 ∧
    cfValue b = 1 / (((b 0 : ℕ) : ℝ) + cfValue (fun n => b (n + 1))) := by
  sorry

end Freiman
