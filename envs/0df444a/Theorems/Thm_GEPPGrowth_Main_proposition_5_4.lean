-- Prove2me | Theorems.Thm_GEPPGrowth_Main_proposition_5_4
-- name    : GEPPGrowth.Main.proposition_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:38:24.290203+00:00
-- url     : https://prove2.me/theorems/e684b7f0-25f2-4e0a-af58-5474a03e8b0e
-- title:
--   Proposition 5.4 — Covariance growth forces a large U entry
-- statement:
--   The matrices $U$ and $\Sigma^{(n-d+1)}$ are computed from the same Gaussian input and its actual elimination history.
--
--   Fix $1\le d\le n$. For every $g>0$, if $U$ is the upper triangular matrix produced by
--   GEPP when run on a matrix of independent $N(0,1)$ variables, and $\Sigma^{(k)}$ is the covariance matrix
--   of the first column of $M^{(k)}$, then
--
--   $$
--   \Pr\left(\max_{i,j}|U[i,j]|\ge\sqrt{\dfrac{g}{2d}}\;\middle|\;\|\Sigma^{(n-d+1)}\|_2\ge g\right)\ge0.47
--   $$,
--
--   provided that $\Pr(\|\Sigma^{(n-d+1)}\|_2\ge g)>0$.
--
--   This relates large covariance to a large entry of the actual final triangular matrix.
--
--   Differences from the source:
--   - encoding: conditional probability on the positive-mass covariance event → joint-event probability divided by the probability of the covariance event; reason: the source positive-probability proviso is retained, so the ratio is precisely the conditional probability
-- source:
--   Daniel Spielman, Xifan Yu, STOC 2027 submission #1176 (October 2026), Proposition 5.4, printed p.20, PDF p.21

import Definitions.Def_GEPPGrowth_Main_Process
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPPGrowth.Main

/-- Proposition 5.4, printed p.20 / PDF p.21. Conditional probability is the ratio of joint to conditioning probability, with the source positive-mass proviso retained. -/
theorem proposition_5_4 (n d : ℕ) (hd : 1 ≤ d) (hdn : d ≤ n)
    (g : ℝ) (hg : 0 < g)
    (hpos : 0 < prob (GaussianMatrix.gaussianMatrix n n)
      {A | g ≤ GaussianMatrix.specNorm (block (actualCov A (n-d)) d)}) :
    (0.47:ℝ) ≤
      prob (GaussianMatrix.gaussianMatrix n n)
        {A | Real.sqrt (g/(2*(d:ℝ))) ≤ maxEntry (upper A) ∧
          g ≤ GaussianMatrix.specNorm (block (actualCov A (n-d)) d)} /
      prob (GaussianMatrix.gaussianMatrix n n)
        {A | g ≤ GaussianMatrix.specNorm (block (actualCov A (n-d)) d)} := by sorry

end GEPPGrowth.Main
