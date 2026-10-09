-- Prove2me | Theorems.Thm_NearlyUnstableHawkes_CIR_proposition_4_1
-- name    : NearlyUnstableHawkes.CIR.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:37:36.14222+00:00
-- url     : https://prove2.me/theorems/596d1b72-2822-468d-9879-36813c7c6645
-- title:
--   Proposition 4.1 — the error process vanishes uniformly in probability
-- statement:
--   Under the Hawkes assumptions and the regime $T(1-a_T)\to\lambda>0$, define $Y^T$ from the rescaled compensated process $\overline M^T_t=M^T_{tT}/T$ and the error kernel $f^T$ by
--
--   $$Y^T_t=\int_0^t f^T(t-u)\,d\overline M^T_u.$$
--
--   Proposition 4.1 states that $Y^T$ converges uniformly in probability to zero on $[0,1]$: for every $\varepsilon>0$, $\mathbb P^T(\sup_{0\le t\le1}|Y^T_t|>\varepsilon)\to0$. It eliminates the error term before passage to the limiting SDE.
--
--   **Formalization Note** The probability spaces may vary with $T$. The supremum is an extended nonnegative supremum, so an unbounded path cannot produce a default zero.
-- source:
--   Jaisson and Rosenbaum, Limit theorems for nearly unstable Hawkes processes, arXiv:1310.2033v2, p. 25, Proposition 4.1; pp. 18, 20–21, definition of f^T and Y^T

import Mathlib
import Definitions.Def_NearlyUnstableHawkes_CIR_Setting

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace NearlyUnstableHawkes.CIR

/-- Proposition 4.1, p. 25: the remainder converges uniformly in probability. -/
theorem proposition_4_1 {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (T a : ℕ → ℝ) (φ φ' : ℝ → ℝ) (m lam μ : ℝ)
    (N : ∀ n, ℝ → Ω n → ℕ)
    (hTpos : ∀ n, 0 < T n)
    (ha0 : ∀ n, 0 < a n) (ha1 : ∀ n, a n < 1)
    (hT : Tendsto T atTop atTop) (ha : Tendsto a atTop (𝓝 1))
    (hμ : 0 < μ) (hlam : 0 < lam)
    (h3 : Tendsto (fun n => T n * (1 - a n)) atTop (𝓝 lam))
    (hφ : Assumption1 φ φ' m) (hρ : Assumption2 T a φ)
    (hN : ∀ n, IsHawkes (P n) μ (fun s => a n * φ s) (T n) (N n)) :
    ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n => P n {ω | ENNReal.ofReal ε <
        ⨆ t : Icc (0 : ℝ) 1,
          ENNReal.ofReal |Y T a φ m lam μ N n t.val ω|})
      atTop (𝓝 0) := by sorry

end NearlyUnstableHawkes.CIR
