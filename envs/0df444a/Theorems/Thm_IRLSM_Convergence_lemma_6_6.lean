-- Prove2me | Theorems.Thm_IRLSM_Convergence_lemma_6_6
-- name    : IRLSM.Convergence.lemma_6_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:52:04.165957+00:00
-- url     : https://prove2.me/theorems/918e63a4-b38b-42f1-bc6c-6809a68bd5f2
-- title:
--   Lemma 6.6 — inverse triangle inequality $\|X-Z\|_*\le\frac{1+\eta}{1-\eta}(\|Z\|_*-\|X\|_*+2\rho_k(X)_*)$, with (6.5)
-- statement:
--   Assume $\mathcal S$ satisfies the strong rank null space property of order $k$ with constant $\eta\in(0,1)$, and let $X,Z$ be matrices with $\mathcal S(X)=\mathcal S(Z)$. Then
--   $$\|X-Z\|_*\le\frac{1+\eta}{1-\eta}\big(\|Z\|_*-\|X\|_*+2\rho_k(X)_*\big).\tag{6.4}$$
--   If moreover $X$ has rank at most $k$, then $\rho_k(X)_*=0$ and
--   $$\|X-Z\|_*\le\frac{1+\eta}{1-\eta}\big(\|Z\|_*-\|X\|_*\big).\tag{6.5}$$
--
--   This inequality is the engine of the recovery results: it converts a gap in nuclear norm into a bound on the distance between feasible matrices.
--
--   **Formalization Note** Real matrices; $\mathcal S$ is given by measurement matrices. The page prints (6.5) with the bracket $\|X\|_*-\|Z\|_*$, which contradicts (6.4) at $\rho_k(X)_*=0$ and is false in general; the form stated here is (6.4) with $\rho_k(X)_*=0$, which is how the proof of Theorem 6.11(i) uses it in (6.9).
-- source:
--   Fornasier, Rauhut, Ward, Low-rank matrix recovery via iteratively reweighted least squares minimization, arXiv:1010.2471v4 (2011), Lemma 6.6, (6.4), p. 17; (6.5), p. 18

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic

open HighDimStat.MatrixRank Matrix

namespace IRLSM.Convergence

/-- **Lemma 6.6 (inverse triangle inequality), with (6.5).** Assume `S` satisfies the SRNSP of
order `k` with constant `η ∈ (0, 1)`, and `S(X) = S(Z)`. Then
`‖X − Z‖_* ≤ (1 + η)/(1 − η) (‖Z‖_* − ‖X‖_* + 2ρ_k(X)_*)` (6.4). If moreover `X` has rank at most
`k`, then `‖X − Z‖_* ≤ (1 + η)/(1 − η) (‖Z‖_* − ‖X‖_*)` (6.5, corrected).

Fornasier–Rauhut–Ward, arXiv:1010.2471v4, Lemma 6.6, (6.4), p. 17; (6.5), p. 18.

Formalization Notes: real matrices; `S` by measurement matrices. **Printed slip:** (6.5) is printed
with the bracket `‖X‖_* − ‖Z‖_*`, which contradicts (6.4) with `ρ_k(X)_* = 0` and is false in general
(its right side is negative for every feasible `Z` with `‖Z‖_* > ‖X‖_*`). The second conjunct is
(6.4) with `ρ_k(X)_* = 0`, the form used in (6.9) of the proof of Theorem 6.11(i). -/
theorem lemma_6_6 {n p m : ℕ} (A : Fin m → Matrix (Fin n) (Fin p) ℝ) (k : ℕ) (η : ℝ)
    (hS : SRNSP A k η) (X Z : Matrix (Fin n) (Fin p) ℝ)
    (hXZ : observationOp A X = observationOp A Z) :
    nuclearNorm (X - Z) ≤ (1 + η) / (1 - η) * (nuclearNorm Z - nuclearNorm X + 2 * rho k X) ∧
      (X.rank ≤ k → nuclearNorm (X - Z) ≤ (1 + η) / (1 - η) * (nuclearNorm Z - nuclearNorm X)) := by sorry

end IRLSM.Convergence
