-- Prove2me | Theorems.Thm_MixScale_lemma_C_1
-- name    : MixScale.lemma_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:10:16.824135+00:00
-- url     : https://prove2.me/theorems/940fb3e4-dc42-4602-8c19-44c8c313067c
-- title:
--   Lemma C.1, pp.21–22 — band covariance
-- statement:
--   Let a scalar law have characteristic function with $|\phi(s)|\le C(1+|s|)^{-q}$, $q>0$. For $R\ge1$ and the midpoint grid of size $n\ge R$, put $U(X)=n^{-1/2}(e^{iRx_\ell X})_\ell$ and $Y(X)=n^{-1/2}((Rx_\ell)^qe^{iRx_\ell X})_\ell$, and $\tau=\min(q,1)$. Then there are $C_q,C'_q$ depending only on $q,C$ with
--
--   $$\|E\,UU^*\|_{\mathrm{op}}\le C_qR^{-\tau}\mathcal L_q(R),\qquad\|\mathrm{Cov}(Y)\|_{\mathrm{op}}\le C'_qR^{2q-\tau}\mathcal L_q(R),\qquad\|Y(X)\|_2\le(2R)^q,$$
--
--   and the covariance of the realified vector satisfies the same bound.
--
--   This governs the noise of the refinement step and produces the factor $R^{2q-\tau}$ in the sample bound.
--
--   Differences from the source:
--   - reading: The covariance bound also holds for the realified vector, up to the same fixed constants → with the same constant C′_q; reason: the paper's proof gives the same constant through a real functional's equal-norm complex functional, and this implies any reading with a larger constant
--   - encoding: ‖·‖_op; E UU∗; Cov(Y) → operator norm on the Euclidean space; entrywise integrals, with E YY∗ − (E Y)(E Y)∗; reason: the same objects
-- source:
--   Wang–Zhang, Learning Mixtures with Unknown Scales: Sharp Dependence on Separation, STOC 2027 submission (sha256 5277f95e…), Lemma C.1, pp.21–22 (PDF pp.23–24)

import Mathlib
import Definitions.Def_MixScale_Profile
import Definitions.Def_MixScale_Scalar

open MeasureTheory

namespace MixScale

/-- **Lemma C.1** (Band covariance).

S. Wang and X. Zhang, *Learning Mixtures with Unknown Scales: Sharp Dependence on Separation*, STOC
2027 submission manuscript (sha256 5277f95e…7c6c), Lemma C.1, pp.21–22 (PDF pp.23–24).

**Formalization Note.** `C_q, C′_q` are chosen after `q, C`, before the distribution, `R` and `n`.
"Up to the same fixed constants": the realified covariance is bounded with the same `C′_q` (the
proof's reduction of a real functional to a complex one of equal coefficient norm). -/
theorem lemma_C_1 (q C : ℝ) (hq : 0 < q) :
    ∃ Cq Cq' : ℝ, 0 < Cq ∧ 0 < Cq' ∧
      ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ],
        (∀ s : ℝ, ‖charFun μ s‖ ≤ C * (1 + |s|) ^ (-q)) →
        ∀ (R : ℝ) (n : ℕ), 1 ≤ R → R ≤ (n : ℝ) →
          opNorm (momentU μ R n) ≤ Cq * R ^ (-min q 1) * Lcal q R ∧
          opNorm (covY μ q R n) ≤ Cq' * R ^ (2 * q - min q 1) * Lcal q R ∧
          (∀ X : ℝ, Real.sqrt (∑ l, ‖featY q R n X l‖ ^ 2) ≤ (2 * R) ^ q) ∧
          opNorm (covYReal μ q R n) ≤ Cq' * R ^ (2 * q - min q 1) * Lcal q R := by sorry

end MixScale
