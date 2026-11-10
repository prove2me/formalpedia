-- Prove2me | Theorems.Thm_GEPPGrowth_Main_proposition_4_16
-- name    : GEPPGrowth.Main.proposition_4_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:38:15.262014+00:00
-- url     : https://prove2.me/theorems/d5a76c91-8bd8-489a-8c89-c9c45c03d6d0
-- title:
--   Proposition 4.16 — Exact determinant update and control
-- statement:
--   All vector norms are Euclidean and $\succeq$ denotes symmetric positive semidefinite difference. The covariance update is the actual deterministic compression defined in §3.
--
--   Fix $1\le k\le n-1$. Let $d:=n-k+1$
--   and $\Sigma^{(k)}$ be a $d\times d$ positive definite matrix. Let $y\ne0\in\mathbb R^d$ be any vector.
--
--   • Set $i=\arg\max |y[j]|$.
--   • Set $r=y/y[i]$.
--   • Set $\Sigma^{(k+1)}=\Pi_1P_{1,i}(I_d-re_i^\top)\Sigma^{(k)}(I_d-e_ir^\top)P_{1,i}^\top\Pi_1^\top$.
--
--   Then,
--
--   $$
--   \det(\Sigma^{(k+1)})=\det(\Sigma^{(k)})\cdot\left(r^\top(\Sigma^{(k)})^{-1}r\right)
--   $$.
--
--   If moreover $\Sigma^{(k)}\succeq I_d$, then
--
--   $$
--   \det(\Sigma^{(k+1)})\le d\cdot\det(\Sigma^{(k)})
--   $$.
--
--   This supplies the exact deterministic determinant update and its dimension-factor bound.
--
--   Differences from the source:
--   - encoding: 1-based finite matrix and vector coordinates → zero-based Fin coordinates and explicitly translated dimensions; reason: a relabeling of every source instance; all arithmetic exponents remain real
--   - encoding: any maximizing pivot coordinate, including ties → a free pivot coordinate with the explicit absolute-maximizer predicate; reason: retains the deterministic source claims on tied vectors as well as the concrete algorithm convention
-- source:
--   Daniel Spielman, Xifan Yu, STOC 2027 submission #1176 (October 2026), Proposition 4.16, printed p.15, PDF p.16

import Definitions.Def_GEPPGrowth_Main_Process
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPPGrowth.Main

/-- Proposition 4.16, printed p.15 / PDF p.16. Full identity and Loewner consequence for every maximizing pivot, not only the smallest-index convention. -/
theorem proposition_4_16 (d : ℕ) (hd : 1 ≤ d) (S : Mat (d+1))
    (hS : S.PosDef) (y : Vec (d+1)) (hy : y ≠ 0)
    (i : Fin (d+1)) (hi : IsMaxPivot y i) :
    (updateAt S y i).det = S.det * (ratiosAt y i ⬝ᵥ (S⁻¹ *ᵥ ratiosAt y i)) ∧
    ((S-1).PosSemidef → (updateAt S y i).det ≤ ((d+1:ℕ):ℝ) * S.det) := by sorry

end GEPPGrowth.Main
