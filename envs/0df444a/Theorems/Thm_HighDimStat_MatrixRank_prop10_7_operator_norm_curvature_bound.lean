-- Prove2me | Theorems.Thm_HighDimStat_MatrixRank_prop10_7_operator_norm_curvature_bound
-- name    : HighDimStat.MatrixRank.prop10_7_operator_norm_curvature_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T23:19:44.045083+00:00
-- url     : https://prove2.me/theorems/a8eaaabc-ce41-4724-81ee-454f729636dc
-- title:
--   An operator-norm error bound for nuclear-norm regularization (Proposition 10.7)
-- statement:
--   **Proposition 10.7.** The nuclear-norm chapter's analog of chunk `09-decomposability`'s
--   Theorem 9.24: a companion, typically tighter bound on the estimation error measured in
--   operator norm rather than Frobenius norm, under a curvature condition on the gradient map.
--
--   Suppose the observation operator $\mathcal X_n$ satisfies the $\Phi^*$-curvature condition
--   (10.20) with curvature parameter $\kappa>0$ and tolerance $\tau_n\ge 0$, and consider a
--   matrix $\Theta^*$ with $\mathrm{rank}(\Theta^*) < \kappa/(64\tau_n)$. Then, conditioned on
--   the event $\mathcal G(\lambda_n) = \{\|\!|\frac1n\mathcal X_n^*(w)|\!\|_2\le\lambda_n/2\}$,
--   any optimal solution $\hat\Theta$ of the M-estimator (10.16) satisfies
--
--   $$
--   \|\!|\hat\Theta-\Theta^*|\!\|_2 \le \frac{3\sqrt2\,\lambda_n}{\kappa}.
--   $$
--
--   As the book's own remark notes, this operator-norm bound is, together with the cone-like
--   constraint (10.15), strictly stronger than the Frobenius-norm bound of Proposition 10.6 (it
--   implies a bound of that form via Cauchy-Schwarz on a rank-$\le 2r$ matrix).
--
--   **Formalization Note** Restated locally in `HighDimStat.MatrixRank`, reusing this mission's
--   own `Core` definitions (`DualCurvatureNuclear`, `opNorm`, `IsNuclearNormLSSolution`), never
--   importing chunk `09`'s draft — the same convention as the goal. `Θstar.rank` is Mathlib's
--   own `Matrix.rank` (the dimension of the column space), matching the book's ordinary
--   matrix-rank notion exactly. `hτn : 0 ≤ τn` is not an addition: the book states it
--   explicitly in the line introducing Eq. (10.20) ("τn ≥ 0 is the tolerance parameter").
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 321 (PDF p. 341), Proposition 10.7, Eq. (10.21)

import Mathlib
import Definitions.Def_HighDimStat_MatrixRank_Core

namespace HighDimStat.MatrixRank

/-- Proposition 10.7 (p. 321): suppose the observation operator `Xn` satisfies the `Φ*`-
curvature condition (10.20) with parameter `κ > 0`, and consider a matrix `Θ*` with
`rank(Θ*) < κ/(64τn)`. Then, conditioned on the event `G(λn) = {|||(1/n)X*ₙ(w)|||₂ ≤ λn/2}`,
any optimal solution to the M-estimator (10.16) satisfies the operator-norm bound
`|||Θ̂ − Θ*|||₂ ≤ 3√2 λn/κ`. -/
theorem prop10_7_operator_norm_curvature_bound {d1 d2 n : ℕ}
    (Xs : Fin n → Matrix (Fin d1) (Fin d2) ℝ) (w : Fin n → ℝ)
    (Θstar Θhat : Matrix (Fin d1) (Fin d2) ℝ) (κ τn lamN : ℝ)
    (hκ : 0 < κ) (hτn : 0 ≤ τn) (hlam : 0 < lamN)
    (hcurv : DualCurvatureNuclear Xs κ τn)
    (hrank : (Θstar.rank : ℝ) < κ / (64 * τn))
    (hsol : IsNuclearNormLSSolution Xs (fun i => traceInner (Xs i) Θstar + w i) lamN Θhat)
    (hG : opNorm ((1 / (n : ℝ)) • observationOpAdjoint Xs w) ≤ lamN / 2) :
    opNorm (Θhat - Θstar) ≤ 3 * Real.sqrt 2 * lamN / κ := by sorry

end HighDimStat.MatrixRank
