-- Prove2me | Theorems.Thm_GEPPGrowth_Main_large_growth_probability
-- name    : GEPPGrowth.Main.large_growth_probability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:39:18.954+00:00
-- url     : https://prove2.me/theorems/fcf9994d-cfc1-4169-88cc-1ee3be326b52
-- title:
--   Theorem 2.2 — lower bound on the probability of large GEPP growth
-- statement:
--   Let $n\ge122$, and $A$ be an $n\times n$ matrix with independent $N(0,1)$ entries. Then,
--   for any
--
--   $$
--   \rho\in\left[100\sqrt n\log(n),\ \dfrac{(\frac75)^{(n-22)/2}}{3\sqrt{42}(n-22)\sqrt{\log(n)}}\right]
--   $$,
--
--   we have
--
--   $$
--   \Pr(\rho(A)\ge\rho)\ge\exp\left(-710\log^2\left(\dfrac\rho{\sqrt n}\right)\log(n)\right)
--   $$.
--
--   Here $\rho(A)$ is the exact-arithmetic final-$U$ growth factor, and every logarithm is natural. The probability is under the full unconditioned continuous Gaussian matrix law. This gives an explicit lower bound on the upper tail, with both endpoints and the constant 710 fixed as in the source.
--
--   Differences from the source:
--   - encoding: arbitrary allowed pivot ties and GEPP on nonsingular inputs → the smallest maximizing row and a total real-division extension on singular inputs; reason: the separate almost-sure regularity and tie-agreement obligation shows equality of the source growth random variable under the full Gaussian law
-- source:
--   Daniel Spielman, Xifan Yu, STOC 2027 submission #1176 (October 2026), Theorem 2.2, printed p.4, PDF p.5

import Definitions.Def_GEPPGrowth_Main_Process
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPPGrowth.Main

/-- Theorem 2.2, printed p.4 / PDF p.5. Full iid continuous standard real Gaussian law, exact final-U growth, both closed threshold endpoints and the constant 710. -/
theorem large_growth_probability (n : ℕ) (hn : 122 ≤ n) (ρ : ℝ)
    (hlo : 100 * Real.sqrt (n:ℝ) * Real.log n ≤ ρ)
    (hhi : ρ ≤ Real.rpow (7/5:ℝ) (((n:ℝ)-22)/2) /
      (3 * Real.sqrt 42 * ((n:ℝ)-22) * Real.sqrt (Real.log n))) :
    Real.exp (-710 * (Real.log (ρ / Real.sqrt (n:ℝ)))^2 * Real.log n) ≤
      prob (GaussianMatrix.gaussianMatrix n n) {A | ρ ≤ growth A} := by sorry

end GEPPGrowth.Main
