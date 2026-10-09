-- Prove2me | Theorems.Thm_LatticeHamSim_CommLR_proposition_13_b
-- name    : LatticeHamSim.CommLR.proposition_13_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:04:04.015803+00:00
-- url     : https://prove2.me/theorems/00f258f7-d97b-4d1d-b1a1-caf4b38817f8
-- title:
--   Proposition 13, (35)–(36), p. 25 — two-interaction decay bounds
-- statement:
--   Under the weighted decay condition (15) with $\zeta,\mu>0$, the next two parts of Proposition 13 state, for arbitrary site sets $P,S$,
--
--   $$\sum_{Q,R:P\sim Q\sim R\sim S}\|h_Q\|\|h_R\|\le\zeta^2\sum_{p\in P}e^{-\mu\operatorname{dist}(p,S)},$$
--
--   $$\sum_{Q,R:P\sim Q\sim R}|Q\cup R|\,\|h_Q\|\|h_R\|e^{-\mu\operatorname{dist}(Q\cup R,S)}\le2\zeta^2\sum_{p\in P}e^{-\mu\operatorname{dist}(p,S)}.$$
--
--   The second bound keeps the exact factor $2$ and the cardinality of the union. These are the two-link estimates used to control the longer series terms.
--
--   **Formalization Note** Empty set distance is zero; the indicator conditions still make the empty-index cases well posed. The sums are over all ordered pairs $(Q,R)$ satisfying the printed overlaps. The matrix norm is the L2 operator norm.
-- source:
--   Haah, Hastings, Kothari and Low, Quantum algorithm for simulating real time evolution of lattice Hamiltonians, arXiv:1801.03922v4, p. 25, Appendix C.3, Proposition 13 (35)–(36)

import Mathlib
import Definitions.Def_LatticeHamSim_CommLR_Setting
open scoped Matrix.Norms.L2Operator

namespace LatticeHamSim.CommLR

attribute [local instance] Classical.propDecidable

/-- Proposition 13, equations (35) and (36). -/
theorem proposition_13_b {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ]
    {q : ℕ} (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (ζ μ : ℝ) (hζ : 0 < ζ) (hμ : 0 < μ)
    (h15 : ∀ x : Λ,
      ∑ X ∈ Finset.univ.filter (fun X : Finset Λ => x ∈ X),
        ‖h X‖ * (X.card : ℝ) ^ 2 *
          Real.exp (μ * Metric.diam (X : Set Λ)) ≤ ζ)
    (P S : Finset Λ) :
    (∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets P Q),
      ∑ R ∈ Finset.univ.filter (fun R : Finset Λ => meets Q R ∧ meets R S),
        ‖h Q‖ * ‖h R‖) ≤
      ζ ^ 2 * ∑ p ∈ P, Real.exp (-(μ * Metric.infDist p (S : Set Λ))) ∧
    (∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets P Q),
      ∑ R ∈ Finset.univ.filter (fun R : Finset Λ => meets Q R),
        ((Q ∪ R).card : ℝ) * ‖h Q‖ * ‖h R‖ *
          Real.exp (-(μ * setDist (Q ∪ R) S))) ≤
      2 * ζ ^ 2 * ∑ p ∈ P, Real.exp (-(μ * Metric.infDist p (S : Set Λ))) := by sorry

end LatticeHamSim.CommLR
