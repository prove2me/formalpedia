-- Prove2me | Theorems.Thm_FracRiccati_Radius_Supplement_theorem_3_3_c_counterexample
-- name    : FracRiccati.Radius.Supplement.theorem_3_3_c_counterexample
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T20:55:43.057257+00:00
-- url     : https://prove2.me/theorems/09eb4ee5-194b-4267-b67e-a12706344f20
-- title:
--   Theorem 3.3(c), Moreover clause (corrected: counterexample to boundary convergence)
-- statement:
--   Set $\alpha=1$, $\lambda=\nu=1/2$ and $\mu=-1$. Let $a_k^+$ be the coefficients with the reflected parameter $-\mu=1$. Then, for every $k\ge1$,
--   $$a_k^+=2^{-k},\qquad a_k=(-1)^{k-1}2^{-k},\qquad R_+=R=2.$$
--   The positive-mirror coefficients are strictly decreasing. Nevertheless, the partial sums at their radius do not converge:
--   $$\nexists z\in\mathbb C:\quad \sum_{k=1}^N a_k2^k\longrightarrow z.$$
--   They alternate between one and zero. This refutes the full claim even when “decreases” means strictly decreasing, without needing a numerical asymptotic example. Convergence here means ordinary convergence in the prescribed index order.
--
--   Differences from the source:
--   - correction: eventually decreasing mirror coefficients imply convergence at the radius → strictly decreasing geometric mirror coefficients can give divergent boundary partial sums; reason: the factor R^k cancels 2^(-k), leaving terms (-1)^(k-1); see DISPROOF.md, item 2
--   - encoding: the expansion converges → convergence means the existence of a limit of initial-segment partial sums; reason: this retains conditional convergence as a possibility and does not replace it by absolute summability
-- source:
--   Callegaro, Grasselli, Pagès, Fast Hybrid Schemes for Fractional Riccati Equations (Rough is not so Tough), arXiv:1805.12587v4, p. 9, Theorem 3.3(c), Moreover clause

import Mathlib
import Definitions.Def_FracRiccati_Radius_Supplement_Psi

namespace FracRiccati.Radius.Supplement

open Filter Topology

/-- Geometric coefficients decrease strictly, but the boundary terms do not tend to zero. -/
theorem theorem_3_3_c_counterexample :
    (∀ k : ℕ, 1 ≤ k → coeff 1 (1/2) 1 (1/2) k = (1/2 : ℂ) ^ k) ∧
    (∀ k : ℕ, 1 ≤ k → coeff 1 (1/2) (-1) (1/2) k =
      (-1 : ℂ) ^ (k - 1) * (1/2 : ℂ) ^ k) ∧
    StrictAntiOn (fun k : ℕ => (coeff 1 (1/2) 1 (1/2) k).re) (Set.Ici 1) ∧
    radius 1 (coeff 1 (1/2) 1 (1/2)) = 2 ∧
    radius 1 (coeff 1 (1/2) (-1) (1/2)) = 2 ∧
    ¬ ∃ z : ℂ, Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
        coeff 1 (1/2) (-1) (1/2) k * (2 : ℂ) ^ k) atTop (nhds z) := by sorry

end FracRiccati.Radius.Supplement
