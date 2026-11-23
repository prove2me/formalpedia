-- Prove2me | Theorems.Thm_LeJEPA_fisherInfo_ge_trace_inv
-- name    : LeJEPA.fisherInfo_ge_trace_inv
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T11:41:58.451628+00:00
-- url     : https://prove2.me/theorems/42e4a934-7088-44be-8f09-1059d6ccfd4e
-- title:
--   Cramér–Rao bound for location: $J(p) \ge \mathrm{tr}(\Sigma^{-1})$, with equality only for $\mathcal N(0,\Sigma)$
-- statement:
--   Let $p$ be a mean-zero, continuously differentiable probability density on $\mathbb{R}^K$ with finite second moments and positive-definite covariance $\Sigma=\int xx^\top p$. Then
--
--   $$J(p)\ \ge\ \operatorname{tr}(\Sigma^{-1}),$$
--
--   with equality if and only if $p$ is the Gaussian density $\mathcal N(0,\Sigma)$.
--
--   This is the Cramér–Rao bound for the location family of $p$. It is the first of the two steps in the proof of the isotropic Gaussian optimality theorem.
-- source:
--   Balestriero and LeCun, LeJEPA: Provable and Scalable Self-Supervised Learning Without the Heuristics, arXiv:2511.08544v3 (2025), Appendix B.4, Lemma 6

import Mathlib
import Definitions.Def_LeJEPA_Basic

open MeasureTheory Matrix Filter Topology
open scoped ENNReal InnerProductSpace

namespace LeJEPA

theorem fisherInfo_ge_trace_inv {K : ℕ} (p : (Fin K → ℝ) → ℝ) (hp : IsMeanZeroDensity p) (hcov : (covMat p).PosDef) :
    ENNReal.ofReal ((covMat p)⁻¹.trace) ≤ fisherInfo p ∧
    (fisherInfo p = ENNReal.ofReal ((covMat p)⁻¹.trace) ↔ p = gaussDensity (covMat p)) := by sorry

end LeJEPA
