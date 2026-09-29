-- Prove2me | Theorems.Thm_OnlinePrimalDual_GeneralPacking_lemma14_2
-- name    : OnlinePrimalDual.GeneralPacking.lemma14_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-21T06:09:43.585831+00:00
-- url     : https://prove2.me/theorems/2d2c7425-6e80-4193-a641-cf9e266af466
-- title:
--   Lemma 14.2 — lower bound for the general packing problem
-- statement:
--   On the explicit instance with single constraint Σ_{j=1}^m (m-j+1)y(j) ≤ 1 (so
--   a(max)/a(min) = m), any online B-competitive algorithm's output y satisfies
--   Σ_{j=1}^m (m-j+1)y(j) ≥ H(m)/B.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 251, Lemma 14.2

import Mathlib
import Definitions.Def_OnlinePrimalDual_GeneralPacking_harmonicNum

namespace OnlinePrimalDual.GeneralPacking

/-- **Lemma 14.2** (p. 251, PDF p. 162) — the lower bound showing the `log(a(max)/a(min))`
additive term of Theorem 14.1 is necessary. Uses the book's own explicit instance directly
(single constraint `∑_{j=1}^m (m-j+1)y(j) ≤ 1`, so `a(max)/a(min) = m`): `y : ℕ → ℝ` is any
online `B`-competitive algorithm's output on this instance, formalized via `hB_competitive`
("after the `j`th round, the optimal offline value is `1/(m-j+1)`, thus the value ... given by a
`B`-competitive algorithm must be at least `1/(B(m-j+1))`", p. 251) requiring the cumulative
output after each round `j` to meet this ratio. The conclusion is the book's own summed bound,
`∑_{j=1}^m (m-j+1)y(j) ≥ H(m)/B`. -/
theorem lemma14_2 (m : ℕ) (hm : 1 ≤ m) (B : ℝ) (hB : 0 < B) (y : ℕ → ℝ)
    (hy_nonneg : ∀ k, 0 ≤ y k)
    (hB_competitive : ∀ j ∈ Finset.Icc 1 m,
      1 / (B * ((m : ℝ) - j + 1)) ≤ ∑ k ∈ Finset.Icc 1 j, y k) :
    harmonicNum m / B ≤ ∑ j ∈ Finset.Icc 1 m, ((m : ℝ) - j + 1) * y j := by sorry

end OnlinePrimalDual.GeneralPacking
