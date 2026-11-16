-- Prove2me | Theorems.Thm_MonoABPWidth_Hierarchy_Supplement_theorem_7_6
-- name    : MonoABPWidth.Hierarchy.Supplement.theorem_7_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:39:22.537714+00:00
-- url     : https://prove2.me/theorems/53bc762c-92c5-4c18-acc3-e61925de0f0d
-- title:
--   Theorem 7.6 — permanent optimum asymptotic
-- statement:
--   For each fixed integer $d_\times\ge2$, let $\operatorname{Opt}(n,d_\times)$ be the minimum leaf count over all real monotone formulas of multiplication depth exactly $d_\times$ computing $\operatorname{per}_n$. Let $\ell_{d_\times}(n)=\ln^{\circ(d_\times-1)}(n)$. Then
--   $$\lim_{n\to\infty}\frac{\operatorname{Opt}(n,d_\times)^{1/n}}{\ell_{d_\times}(n)}=\exp(1).$$
--   This is the full two-sided optimum asymptotic $((e+o(1))\ell_{d_\times}(n))^n$ with leading constant $e$, not a one-sided or logarithmic-order estimate. Theorem 7.5 ensures the optimum is finite at positive $n$; iterated logarithms are positive eventually. No rate or uniformity in growing depth is claimed.
--
--   Differences from the source:
--
--   - encoding: optimal leaves ((e+o(1)) ln iterated d-1 times(n))^n → Tendsto of the nth root divided by iterated natural log to exp(1); reason: this is the full two-sided asymptotic; the true feasible-set optimum is finite for positive n by Theorem 7.5, so conversion to real loses no value
--   - encoding: optimal leaf count under the alternating convention of §2.3 → permanentOpt takes the infimum over all computing formula trees of exact multiplication depth d; reason: contracting adjacent gates and then padding with unary alternating gates preserves leaves and restores exact multiplication depth d; hence the alternating and unrestricted optima agree
-- source:
--   Julian Dörfler, Alexander Rogovskyy, STOC 2027 submission #927 (October 2026), Theorem 7.6, p.22, PDF23

import Definitions.Def_MonoABPWidth_Hierarchy_Supplement_permanent

open scoped BigOperators ENNReal

namespace MonoABPWidth.Hierarchy.Supplement

/-- Theorem 7.6, p.22 (PDF23): the full two-sided optimal-leaf
asymptotic with leading constant exp(1), for each fixed multiplication depth. -/
theorem theorem_7_6 (d : ℕ) (hd : 2 ≤ d) :
    Filter.Tendsto (fun n : ℕ =>
      (permanentOpt n d).toReal ^ (1 / (n : ℝ)) / iteratedLog d (n : ℝ))
      Filter.atTop (nhds (Real.exp 1)) := by sorry

end MonoABPWidth.Hierarchy.Supplement
