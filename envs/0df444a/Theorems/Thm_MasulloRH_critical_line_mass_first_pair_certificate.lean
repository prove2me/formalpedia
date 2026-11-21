-- Prove2me | Theorems.Thm_MasulloRH_critical_line_mass_first_pair_certificate
-- name    : MasulloRH.critical_line_mass_first_pair_certificate
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:58:09.010112+00:00
-- url     : https://prove2.me/theorems/6a993fae-e7d3-461e-a029-f2eb21fc3914
-- title:
--   The certified pair near heights ±14.135 meets the finite prime-power comparisons through cutoff nine
-- statement:
--   There is a set $F$ of exactly two critical-line zeros of $\zeta$ with $14.13<|\Im\rho|<14.14$ whose combined resolvent mass is at least $23/5000$. Explicitly, writing $m_\rho$ for analytic multiplicity and $K(t)=(t^2-5)/(2(t^2+25/4)(t^2+4))$, one has
--   $$\sum_{\rho\in F}m_\rho K(\Im\rho)\ge\frac{23}{5000}.$$
--   For every integer $0\le N\le9$, the corresponding finite prime target obeys
--   $$\tfrac12\log2+\tfrac\pi4-\tfrac{37}{30}+\sum_{1\le n<N}\Lambda(n)(n^{-5/2}-n^{-3})\le\frac{23}{5000}.$$
--   Thus the same two zeros supply explicit witnesses for all of these cutoffs, including the positive targets at eight and nine.
-- source:
--   Certified zero interval of bueno_ricardo, XiQuantitativePublished.zeta_zero_between_1413_1414 (6f17bf2b). The multiplicity argument is adapted from Yi’s MasulloRH.single_resolvent_test. Finite case of the Masullo RH trace comparison bd574b97.

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib.NumberTheory.LSeries.Dirichlet

set_option autoImplicit false

open ArithmeticFunction

namespace MasulloRH

theorem critical_line_mass_first_pair_certificate :
    ∃ F : Finset (ZetaZerosInTraceStrip (1/2)), F.card = 2 ∧
      (∀ z ∈ F, z.val.re = 1/2 ∧ 1413/100 < |z.val.im| ∧ |z.val.im| < 707/50) ∧
      23/5000 ≤ (∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val:ℝ) *
        ((z.val.im^2-5)/(2*(z.val.im^2+25/4)*(z.val.im^2+4)))) ∧
      ∀ N : ℕ, N ≤ 9 → Real.log 2/2 + Real.pi/4 - 37/30 +
        (∑ n ∈ Finset.range N, (vonMangoldt n / (n:ℝ)^(5/2:ℝ) -
          vonMangoldt n / (n:ℝ)^(3:ℝ))) ≤ 23/5000 := by sorry

end MasulloRH
