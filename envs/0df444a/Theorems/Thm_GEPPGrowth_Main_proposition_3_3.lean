-- Prove2me | Theorems.Thm_GEPPGrowth_Main_proposition_3_3
-- name    : GEPPGrowth.Main.proposition_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:38:06.121296+00:00
-- url     : https://prove2.me/theorems/c3001a76-2c02-4627-bc76-c839d5884849
-- title:
--   Proposition 3.3 — Compression preserves the relevant spectral norm
-- statement:
--   The covariance is positive semidefinite and the residual column is nonzero, so the source ratio is defined. Both matrix norms are induced Euclidean operator norms.
--
--   $$
--   \|\Sigma^{(k+1)}\|_2=\|(I-re_i^\top)\Sigma^{(k)}(I-e_ir^\top)\|_2
--   $$.
--
--   This identifies the operator norm retained by the actual update.
--
--   Differences from the source:
--   - encoding: 1-based finite matrix and vector coordinates → zero-based Fin coordinates and explicitly translated dimensions; reason: a relabeling of every source instance; all arithmetic exponents remain real
--   - encoding: the defined ratio r=y/y[i] in the actual update → explicit nonzero residual column and positive semidefinite covariance; reason: states the source defined-input domain; the excluded zero column is null for every positive definite process covariance
--   - encoding: any maximizing pivot coordinate, including ties → a free pivot coordinate with the explicit absolute-maximizer predicate; reason: retains the deterministic source claims on tied vectors as well as the concrete algorithm convention
-- source:
--   Daniel Spielman, Xifan Yu, STOC 2027 submission #1176 (October 2026), Proposition 3.3, printed p.7, PDF p.8

import Definitions.Def_GEPPGrowth_Main_Process
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPPGrowth.Main

/-- Proposition 3.3, printed p.7 / PDF p.8. Every maximizing pivot coordinate, including ties; actual update with zero pivot row and column. -/
theorem proposition_3_3 (d : ℕ) (S : Mat (d+1)) (hS : S.PosSemidef)
    (y : Vec (d+1)) (hy : y ≠ 0) (i : Fin (d+1)) (hi : IsMaxPivot y i) :
    GaussianMatrix.specNorm (updateAt S y i) =
      GaussianMatrix.specNorm (eliminationAt y i * S * (eliminationAt y i).transpose) := by sorry

end GEPPGrowth.Main
