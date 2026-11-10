-- Prove2me | Theorems.Thm_GEPPGrowth_Main_proposition_5_2
-- name    : GEPPGrowth.Main.proposition_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:38:02.643235+00:00
-- url     : https://prove2.me/theorems/0e4a36d9-2275-41e8-951e-3c761690c4a6
-- title:
--   Proposition 5.2 — One-step covariance growth probability
-- statement:
--   The current covariance is fixed and the probability is over one fresh Gaussian column; it is not over an arbitrarily chosen next covariance.
--
--   Fix $1\le k\le n-3$. Let $d:=n-k+1$ and $\Sigma^{(k)}\succeq I_d$ be a $d\times d$ positive-definite
--   matrix. Let $\Sigma^{(k+1)}\in\mathbb R^{(d-1)\times(d-1)}$ be obtained from $\Sigma^{(k)}$ according to the covariance update process
--   as in Proposition 3.1. Then,
--
--   $$
--   \Pr\left(\|\Sigma^{(k+1)}\|_2\ge\left(\dfrac32-\dfrac2d\right)\|\Sigma^{(k)}\|_2\right)\ge\dfrac{0.16^d}{2d\cdot\sqrt{\det(\Sigma^{(k)})}}
--   $$.
--
--   This quantifies one-step growth at an arbitrary current state in the source domain.
--
--   Differences from the source:
--   - encoding: 1-based finite matrix and vector coordinates → zero-based Fin coordinates and explicitly translated dimensions; reason: a relabeling of every source instance; all arithmetic exponents remain real
--   - encoding: a maximizing pivot with arbitrary ties → an arbitrary maximizing selector, with outer probability and no measurability hypothesis on that selector; reason: retains every tie resolution; the source positive definite Gaussian laws give zero mass to tie columns
-- source:
--   Daniel Spielman, Xifan Yu, STOC 2027 submission #1176 (October 2026), Proposition 5.2, printed p.17, PDF p.18

import Definitions.Def_GEPPGrowth_Main_Process
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPPGrowth.Main

/-- Proposition 5.2, printed p.17 / PDF p.18. Any maximizing selector at any source current state; exact determinant dependence. -/
theorem proposition_5_2 (d : ℕ) (hd : 3 ≤ d) (S : Mat (d+1))
    (hS : S.PosDef) (hI : (S-1).PosSemidef)
    (p : Vec (d+1) → Fin (d+1))
    (hmax : ∀ y, IsMaxPivot y (p y)) :
    (0.16:ℝ)^(d+1) / (2*((d+1:ℕ):ℝ)*Real.sqrt S.det) ≤
      prob (normal S) {y | (3/2 - 2/((d+1:ℕ):ℝ))*GaussianMatrix.specNorm S ≤
        GaussianMatrix.specNorm (updateAt S y (p y))} := by sorry

end GEPPGrowth.Main
