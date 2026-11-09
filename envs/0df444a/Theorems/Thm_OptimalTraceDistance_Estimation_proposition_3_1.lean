-- Prove2me | Theorems.Thm_OptimalTraceDistance_Estimation_proposition_3_1
-- name    : OptimalTraceDistance.Estimation.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T05:44:59.752092+00:00
-- url     : https://prove2.me/theorems/41ae58ea-92b2-427a-a298-fbb67879fd99
-- title:
--   Proposition 3.1 — bias bound
-- statement:
--   Let $d\ge2$, $0<\varepsilon\le1/32$, let $\rho,\sigma$ be arbitrary density matrices, and let $Q$ be an orthogonal projector with $\operatorname{rank}(I-Q)\le2\log d$. For the full expression $f$ in (27),
--   $$|f(S_+,S_-)-d_{\rm tr}(\rho,\sigma)|\le\varepsilon/4.$$
--   The correction retains the entire difference between the two traces. No small operator-norm condition is assumed in this bias statement.
--
--   Differences from the source:
--   - encoding: Positive-dimensional complex matrices and source trace expressions → Fin d matrices; retained ordered words; real parts of real traces; explicit finite index sums; reason: Indexing and real extraction preserve all source instances; no rank or commutativity restriction is added
--   - encoding: Sufficiently large universal C0 and the fixed multiscale construction → C0=2^40 and A=2^30; reason: p.25 gives scalar error 32/K and p.26 gives perturbation error 64 rank/K; these choices exceed all bias requirements in the p.12 proof
-- source:
--   Ziyun Chen, Minbo Gao, Qisheng Wang, STOC 2027 submission #875 (October 2026), Proposition 3.1, p. 12.

import Definitions.Def_OptimalTraceDistance_Estimation_Algorithm2

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal ComplexOrder
noncomputable section

namespace OptimalTraceDistance.Estimation

theorem proposition_3_1 (d : ℕ) (hd : 2 ≤ d) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1/32)
    (ρ σ : Mat d) (hρ : Density ρ) (hσ : Density σ)
    (Q : Mat d) (hQ : projector Q) (hrank : ((1-Q).rank : ℝ) ≤ 2*Real.log d) :
  |(evaluate (f d ε Q) (plus ρ σ) (minus ρ σ)).re - distance ρ σ| ≤ ε/4 := by sorry

end OptimalTraceDistance.Estimation
