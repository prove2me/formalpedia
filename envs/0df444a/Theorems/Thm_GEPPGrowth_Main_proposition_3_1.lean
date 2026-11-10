-- Prove2me | Theorems.Thm_GEPPGrowth_Main_proposition_3_1
-- name    : GEPPGrowth.Main.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:38:04.90073+00:00
-- url     : https://prove2.me/theorems/f1f2fdd4-feb4-453f-b3f0-ba568d0d4627
-- title:
--   Proposition 3.1 — Conditional Gaussian residual columns
-- statement:
--   Here $M^{(k)}$ is a square residual matrix; its covariance is positive semidefinite. The update and pivot conventions are those of §3.
--
--   Let the columns of $M^{(k)}$ be independent $N(0,\Sigma^{(k)})$ vectors. Then, conditioning
--   on the first column $y$ of $M^{(k)}$, the columns of $M^{(k+1)}$ are independent $N(0,\Sigma^{(k+1)})$ vectors, where
--   $\Sigma^{(k+1)}$ may be obtained by
--
--   • sampling $y\sim N(0,\Sigma^{(k)})$,
--   • setting the pivot $i=\arg\max |y[i]|$,
--   • defining $r=y/y[i]$,
--   • and setting $\Sigma^{(k+1)}=\Pi_1P_{1,i}(I-re_i^\top)\Sigma^{(k)}(I-e_ir^\top)P_{1,i}^\top\Pi_1^\top$.
--
--   This is the distributional link between elimination and the covariance transition.
--
--   Differences from the source:
--   - encoding: 1-based finite matrix and vector coordinates → zero-based Fin coordinates and explicitly translated dimensions; reason: a relabeling of every source instance; all arithmetic exponents remain real
--   - encoding: conditional independence of the remaining Gaussian columns → equality of joint measures with an explicitly integrated product Gaussian kernel; reason: equivalent disintegration statement, including singular positive semidefinite covariances
--   - encoding: the first-column maximizing pivot in a conditional-law assertion → an arbitrary measurable maximizing selector of that column; reason: makes the random-variable convention explicit and covers every such tie resolution, including singular covariance laws
--   - encoding: quotient r=y/y[i] where the pivot entry is nonzero → total real division with r=0 at y=0; reason: agrees on every defined source input; the zero-column event is null for every nonzero positive semidefinite covariance, and S=0 has deterministic zero columns
-- source:
--   Daniel Spielman, Xifan Yu, STOC 2027 submission #1176 (October 2026), Proposition 3.1, printed p.7, PDF p.8

import Definitions.Def_GEPPGrowth_Main_Process
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPPGrowth.Main

/-- Proposition 3.1, printed p.7 / PDF p.8. Every measurable maximizing pivot selector, including all allowed tie choices; joint-law identity records conditional independence. -/
theorem proposition_3_1 (d : ℕ) (S : Mat (d+1)) (hS : S.PosSemidef)
    (p : Vec (d+1) → Fin (d+1)) (hp : Measurable p)
    (hmax : ∀ y, IsMaxPivot y (p y)) :
    (columnsLaw S (d+1)).map
      (fun M => ((fun i => M i 0), residualStepWith p M)) =
    (normal S).bind (fun y => (columnsLaw (updateAt S y (p y)) d).map (fun M => (y,M))) := by sorry

end GEPPGrowth.Main
