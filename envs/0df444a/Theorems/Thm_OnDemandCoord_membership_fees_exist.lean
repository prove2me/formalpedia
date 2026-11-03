-- Prove2me | Theorems.Thm_OnDemandCoord_membership_fees_exist
-- name    : OnDemandCoord.membership_fees_exist
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:22:39.551999+00:00
-- url     : https://prove2.me/theorems/a2197516-42d7-4a1d-b3ec-8f6f19c1f6ce
-- title:
--   Existence of membership fees (corrected: (16′) in place of (16))
-- statement:
--   **Existence of membership fees** (p. 22). Let $Q^p$ satisfy $p\bar F_i(Q^p_i)=c$ for all $i$ and let $(Q^*,\eta^*)$ be a system optimum, with $m_i$ from (14). Then there are fees $r_1,\dots,r_n$ satisfying (16′),
--   $$\sum_ir_i\ \ge\ C(Q^*,\eta^*)-c\sum_iQ^*_i-p\sum_i(1-m_i)\,\mathbb E[(X_i-Q^*_i)^+],$$
--   and (17) for every firm,
--   $$r_i\ \le\ h^p_i-\big(p(1-m_i)\,\mathbb E[(X_i-Q^*_i)^+]+cQ^*_i\big).$$
--
--   The reason is that the system optimum costs no more than staffing without the platform: $C(Q^*,\eta^*)\le C(Q^p,\underline\tau)=\sum_ih^p_i$.
--
--   Differences from the source:
--   - encoding: the model of §3 (continuous nonnegative demands with finite mean, any joint law; G continuous, log-concave, with density g > 0 on [τ̲, τ̄]) → OnDemandCoord.Model: X_i measurable, integrable, ≥ 0 a.s., atomless law; G continuous, monotone, 0 left of τ̲, 1 right of τ̄, G′ = g > 0 within [τ̲, τ̄], log G concave on (τ̲, τ̄]; reason: readings of the standing assumptions, stated once on the definition; no instance of the paper is excluded
--   - correction: there exist fees satisfying (16) and (17) → there exist fees satisfying (16′) and (17); reason: with printed (16) the sentence is false: n = 1, X ~ Exp(1), p = 2, c = 1, G uniform on [0.95, 1.95], N = 10 gives (16) r ≥ 0.6869 and (17) r ≤ 0.25 (paper.md item 1)
--   - generalization: under the standing assumption τ̲ < φ^p of §5 → no such assumption; reason: C(Q*, η*) ≤ Σ h^p_i holds at every system optimum
--   - reading: Q* as in Theorem 1 → any global minimizer of (5); reason: p. 10's definition of the system optimum
-- source:
--   Lu–Zheng–Zhong, Maximizing the Benefits of an On-Demand Workforce: Fill Rate-Based Allocation and Coordination Mechanisms, SSRN:2783617 (PDF of 2023-05-13; article doi:10.1287/msom.2021.0327), pp. 21–22, (16)–(17) and the sentence before Theorem 2

import Mathlib
import Definitions.Def_OnDemandCoord_Coordinates

namespace OnDemandCoord

open MeasureTheory ProbabilityTheory

/-- **Existence of membership fees, corrected**, Lu–Zheng–Zhong, SSRN:2783617 (PDF of 2023-05-13), p. 22. At a system optimum, with `m_i`
from (14), some fees `r` satisfy (16′) and (17). The printed (16) can have no solution with (17).

**Formalization Note.** The standing assumption `τ̲ < φ^p` of §5 is not needed: the fees exist because
`C(Q*, η*) ≤ C(Q^p, τ̲) = ∑_i h_i^p` at every system optimum. -/
theorem membership_fees_exist {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} (M : Model Ω P n)
    (Qp : Fin n → ℝ) (hQp : M.IsPermanentBenchmark Qp)
    (Qstar : Fin n → ℝ) (ηstar : ℝ) (hopt : M.IsSystemOptimum Qstar ηstar) :
    ∃ r : Fin n → ℝ, M.FeeLower Qstar ηstar (M.mParam Qstar) r ∧
      ∀ i, M.FeeUpper Qp Qstar (M.mParam Qstar) r i := by sorry

end OnDemandCoord
