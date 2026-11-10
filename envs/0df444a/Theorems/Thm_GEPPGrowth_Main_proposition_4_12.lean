-- Prove2me | Theorems.Thm_GEPPGrowth_Main_proposition_4_12
-- name    : GEPPGrowth.Main.proposition_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:38:05.930289+00:00
-- url     : https://prove2.me/theorems/f647de72-4ae4-4fa6-bee2-61579e4daadf
-- title:
--   Proposition 4.12 — Sufficient condition for covariance growth
-- statement:
--   The vector $v$ has Euclidean length one and satisfies $\Sigma^{(k)}v=\|\Sigma^{(k)}\|_2v$. All norms and deleted-coordinate inner products have their Euclidean meaning.
--
--   Fix $1\le k\le n-1$. Let $d:=n-k+1$ and $\Sigma^{(k)}$ be a $d\times d$ positive definite matrix. Let $v\in\mathbb R^d$ be a top unit eigenvector of $\Sigma^{(k)}$.
--   Let $y\ne0\in\mathbb R^d$ be any vector.
--
--   • Set $i=\arg\max |y[j]|$.
--   • Set $r=y/y[i]$.
--   • Set $\Sigma^{(k+1)}=\Pi_1P_{1,i}(I_d-re_i^\top)\Sigma^{(k)}(I_d-e_ir^\top)P_{1,i}^\top\Pi_1^\top$.
--
--   If for some $C\ge1$, (1) $v[i]^2\ge\dfrac1d$, (2) $\|r\|_2^2\ge\dfrac dC\ge2$, and (3) $v[i]\langle v[-i],r[-i]\rangle\le0$, then
--
--   $$
--   \|\Sigma^{(k+1)}\|_2\ge\left(1+\dfrac1C-\dfrac2d\right)\|\Sigma^{(k)}\|_2
--   $$.
--
--   This is the stated sufficient condition for one-step covariance growth.
--
--   Differences from the source:
--   - encoding: 1-based finite matrix and vector coordinates → zero-based Fin coordinates and explicitly translated dimensions; reason: a relabeling of every source instance; all arithmetic exponents remain real
--   - encoding: any maximizing pivot coordinate, including ties → a free pivot coordinate with the explicit absolute-maximizer predicate; reason: retains the deterministic source claims on tied vectors as well as the concrete algorithm convention
-- source:
--   Daniel Spielman, Xifan Yu, STOC 2027 submission #1176 (October 2026), Proposition 4.12, printed p.10, PDF p.11

import Definitions.Def_GEPPGrowth_Main_Process
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPPGrowth.Main

/-- Proposition 4.12, printed p.10 / PDF p.11. Every maximizing pivot; all sufficient conditions, with the source fraction D/C. -/
theorem proposition_4_12 (d : ℕ) (hd : 1 ≤ d) (S : Mat (d+1)) (hS : S.PosDef)
    (v : Vec (d+1)) (hv : sqLength v = 1)
    (heig : S *ᵥ v = GaussianMatrix.specNorm S • v)
    (y : Vec (d+1)) (hy : y ≠ 0) (i : Fin (d+1)) (hi : IsMaxPivot y i)
    (C : ℝ) (hC : 1 ≤ C)
    (hcoord : 1/((d+1:ℕ):ℝ) ≤ v i^2)
    (hlen : ((d+1:ℕ):ℝ)/C ≤ sqLength (ratiosAt y i))
    (hlarge : 2 ≤ ((d+1:ℕ):ℝ)/C)
    (hsign : v i * deletedInner i v (ratiosAt y i) ≤ 0) :
    (1 + 1/C - 2/((d+1:ℕ):ℝ)) * GaussianMatrix.specNorm S ≤
      GaussianMatrix.specNorm (updateAt S y i) := by sorry

end GEPPGrowth.Main
