-- Prove2me | Theorems.Thm_OptInapprox_Bal2Sat_Supplement_theorem_8
-- name    : OptInapprox.Bal2Sat.Supplement.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:01:08.019809+00:00
-- url     : https://prove2.me/theorems/08cae634-bf81-42c3-9228-cea896785b09
-- title:
--   Theorem 8 — exact plurality limit and Frieze–Jerrum Gaussian competition
-- statement:
--   Fix an integer $q\ge2$ and a real $\rho$ with $-1/(q-1)\le\rho\le1$. Let $\mathrm{Plurality}_{n,q}$ output a most-frequent symbol, embedded as a simplex vertex. For $q$ independent centered normal pairs $(U_i,V_i)$, each having variances one and covariance $\rho$, put $I(q,\rho)=\Pr[U_0=\max_i U_i,\ V_0=\max_i V_i]$. Then
--
--   $$\lim_{n\to\infty}S_\rho(\mathrm{Plurality}_{n,q})=qI(q,\rho),\qquad I(q,\rho)=\frac{P_q(\rho)}q=I_{\mathrm{FJ}}(q,\rho).$$
--
--   Here $P_q$ is the published Frieze–Jerrum k-spokes collision probability with $k=q$, under the product of two standard Gaussian vectors. The identity therefore retains the final identification in Theorem 8 and its single-colour normalization. All natural input dimensions tend to infinity; no finite-dimensional balance is assumed. The endpoint laws, including $q=2,\rho=-1$ and $\rho=1$, remain included.
--
--   Differences from the source:
--   - encoding: arbitrary plurality tie-breaking → least maximizing symbol at each finite n; reason: the source says tie-breaking is unimportant; ties have probability tending to zero
--   - encoding: q correlated normal pairs and Frieze–Jerrum I(ρ) → q independent copies of the published stdGaussPair transformed by V=ρU+√(1−ρ²)Z, and the published k-spokes collision probability divided by q; reason: these have exactly the required covariance and single-colour normalization, including singular endpoints
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 13, Theorem 8; proof pp. 29–30

import Mathlib
import Definitions.Def_OptInapprox_Bal2Sat_Supplement_Plurality

namespace OptInapprox.Bal2Sat.Supplement

theorem theorem_8 (q : ℕ) (hq : 2 ≤ q) (ρ : ℝ)
    (hρ : -(1 / ((q : ℝ) - 1)) ≤ ρ ∧ ρ ≤ 1) :
    Filter.Tendsto (fun n : ℕ => qStability ρ
      (pluralityVector (q := q) (n := n) (by omega)))
      Filter.atTop (nhds ((q : ℝ) * gaussianContest q (by omega) ρ)) ∧
    gaussianContest q (by omega) ρ = friezeJerrumI q ρ := by sorry

end OptInapprox.Bal2Sat.Supplement
