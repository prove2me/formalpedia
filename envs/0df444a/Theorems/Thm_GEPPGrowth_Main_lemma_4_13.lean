-- Prove2me | Theorems.Thm_GEPPGrowth_Main_lemma_4_13
-- name    : GEPPGrowth.Main.lemma_4_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:38:04.948777+00:00
-- url     : https://prove2.me/theorems/40353504-91bd-4381-b978-1cf53c05c3b7
-- title:
--   Lemma 4.13 — Covariance determinant formula
-- statement:
--   The conditioning is on original input columns. Pivot row indices remain the labels of the original matrix; the square pivot minor can be ordered in pivot order because its determinant is squared.
--
--   Fix $2\le k\le n$. Consider the execution of GEPP on an
--   $n\times n$ matrix $A$ with independent $N(0,1)$ entries after $k-1$ steps. Let $P\subseteq[n]$ be the set of $k-1$
--   row indices of $A$ chosen as pivots in the first $k-1$ steps by GEPP. Then, conditioning on the first
--   $k-1$ columns of $A$, every column of the residual matrix $M^{(k)}=A^{(k)}[k:n,k:n]$ is independently
--   distributed as $N(0,\Sigma^{(k)})$, and
--
--   $$
--   \det(\Sigma^{(k)})=\dfrac{\det(A[:,1:(k-1)]^\top A[:,1:(k-1)])}{\det(A[P,1:(k-1)])^2}
--   $$.
--
--   This connects residual covariance determinants to adaptively selected input minors.
--
--   Differences from the source:
--   - encoding: source step k and covariance Σ^(k) → time k-1 with a zero-padded state and active leading block of dimension n-(k-1); reason: the leading block has exactly the source dimension n-k+1, with the explicit Gaussian transition law
--   - encoding: conditioning on original columns and the adaptively selected row set → measurable-history integral identity and an almost-sure determinant identity using pivot-ordered original labels; reason: conditioning on a single Gaussian history has zero probability; squaring removes the row-order sign
-- source:
--   Daniel Spielman, Xifan Yu, STOC 2027 submission #1176 (October 2026), Lemma 4.13, printed p.10, PDF p.11

import Definitions.Def_GEPPGrowth_Main_Process
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace GEPPGrowth.Main

/-- Lemma 4.13, printed p.10 / PDF p.11. The denominator uses actual adaptively chosen original row labels, in pivot order; its squared determinant is independent of this ordering. -/
theorem lemma_4_13 (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n) :
    HasResidualLaw n (k-1) (by omega) ∧
    (∀ᵐ A ∂(GaussianMatrix.gaussianMatrix n n),
      (block (actualCov A (k-1)) (n-(k-1))).det =
        ((firstColumns (show k-1 ≤ n by omega) A).transpose *
          firstColumns (show k-1 ≤ n by omega) A).det /
        (pivotMinor (show k-1 ≤ n by omega) A).det ^ 2) := by sorry

end GEPPGrowth.Main
