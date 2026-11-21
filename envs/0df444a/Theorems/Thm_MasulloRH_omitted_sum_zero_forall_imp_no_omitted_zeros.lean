-- Prove2me | Theorems.Thm_MasulloRH_omitted_sum_zero_forall_imp_no_omitted_zeros
-- name    : MasulloRH.omitted_sum_zero_forall_imp_no_omitted_zeros
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T23:32:30.971891+00:00
-- url     : https://prove2.me/theorems/a594e811-ec76-475d-9a49-e495f4112c6e
-- title:
--   Mellin separation: vanishing of the omitted sum for all tests forces the omitted zero set empty (RH-strength)
-- statement:
--   Let $0 < \alpha < 1/2$. Suppose that for every rational trace test function $\varphi$ — smooth, compactly supported in the positive reals, and vanishing at $1$ — the multiplicity-weighted Mellin sum over the critical zeros of the Riemann zeta function on or outside the window boundary, $|\Re\rho - \tfrac12| \ge \alpha$, vanishes. Then there are no omitted zeros: every critical zero $\rho$ satisfies $|\Re\rho - \tfrac12| < \alpha$.
--
--   This is the Mellin-separation step of the rational trace formula: the Mellin transforms of the admissible tests separate the points of the critical strip, so a discrete spectral measure on the omitted zeros that pairs to zero with every test must be the zero measure. **It is stated plainly that this assertion is of Riemann-hypothesis strength**: combined with the vanishing node `MasulloRH.narrow_window_omitted_zero_sum` it is equivalent, over the proved explicit formula, to the absence of zeta zeros off the critical line. It is not a lemma of elementary analysis, and no proof of it is known that does not in substance prove a zero-free statement of Riemann-hypothesis strength. The node is proposed because naming the implication makes the equivalence *trace formula $\Leftrightarrow$ zero-freeness* a citable platform object; it is not proposed as an easier target than `MasulloRH.zero_free_right`.
-- source:
--   Derived separation consequence in the context of A. M. Masullo, The Music of the Primes, 20 November 2026 draft, Theorem 12.5.1.1, pp. 519-520. Platform nodes linked: antecedent = conclusion of MasulloRH.narrow_window_omitted_zero_sum (6d631fe7-ce53-4f51-b660-706b2183ed5d, Open), split off from the proved MasulloRH.trace_window_comparison (49251e54-b1ef-4313-9a30-285f84fc789c); summability input ConnesRZ.actual_zero_reciprocal_square_summable (de16ef44-c04f-4b8a-ba99-8107f9af4d39, Proved); equivalent zero-free form MasulloRH.zero_free_right (12360d46-f4ac-4dcc-93d2-06be16c15a38, Open).

import Definitions.Def_MasulloRH_RationalTrace
import Definitions.Def_ConnesRZ_weil_defs
open MeasureTheory Set MasulloRH ConnesRZ

theorem MasulloRH.omitted_sum_zero_forall_imp_no_omitted_zeros (α : ℝ) (hα : 0 < α) (hα2 : α < 1/2) :
    (∀ (φ : ℝ → ℂ), IsRationalTraceTest φ →
      (let omitted := {ρ : {z : ℂ // ConnesRZ.IsCriticalZero z} | α ≤ |ρ.val.re - 1/2|}
       (∑' r : omitted, (ConnesRZ.zeroMult r.val.val : ℂ) * mellin φ (r.val.val - 1/2)) = 0)) →
    ∀ ρ : {z : ℂ // ConnesRZ.IsCriticalZero z}, |ρ.val.re - 1/2| < α := by sorry
