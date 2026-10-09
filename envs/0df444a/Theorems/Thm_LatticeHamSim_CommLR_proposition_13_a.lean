-- Prove2me | Theorems.Thm_LatticeHamSim_CommLR_proposition_13_a
-- name    : LatticeHamSim.CommLR.proposition_13_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:03:53.875762+00:00
-- url     : https://prove2.me/theorems/f5eca25a-fb67-4aab-9e9d-0861839b4487
-- title:
--   Proposition 13, (33)–(34), p. 25 — one-interaction decay bounds
-- statement:
--   Assume the exponential decay condition (15) with $\zeta,\mu>0$. For arbitrary site sets $P,S$, Proposition 13 first gives
--
--   $$\sum_{Q:P\sim Q\sim S}\|h_Q\|\le\zeta\sum_{p\in P}e^{-\mu\operatorname{dist}(p,S)},\qquad\sum_{Q:P\sim Q}\|h_Q\|\,|Q|^2e^{-\mu\operatorname{dist}(Q,S)}\le\zeta\sum_{p\in P}e^{-\mu\operatorname{dist}(p,S)}.$$
--
--   These estimates convert the weighted local decay assumption into bounds on one interaction set, with or without an overlap with the target set.
--
--   **Formalization Note** Site sets are finite. Set-to-set distance is the minimum over pairs when both sets are nonempty, and zero otherwise; the stated inequalities remain valid at empty sets. The matrix norm is the L2 operator norm. No Hermitian or support assumption is needed beyond the numerical norms appearing in (15).
-- source:
--   Haah, Hastings, Kothari and Low, Quantum algorithm for simulating real time evolution of lattice Hamiltonians, arXiv:1801.03922v4, p. 25, Appendix C.3, Proposition 13 (33)–(34)

import Mathlib
import Definitions.Def_LatticeHamSim_CommLR_Setting
open scoped Matrix.Norms.L2Operator

namespace LatticeHamSim.CommLR

attribute [local instance] Classical.propDecidable

/-- Proposition 13, equations (33) and (34). -/
theorem proposition_13_a {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ]
    {q : ℕ} (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (ζ μ : ℝ) (hζ : 0 < ζ) (hμ : 0 < μ)
    (h15 : ∀ x : Λ,
      ∑ X ∈ Finset.univ.filter (fun X : Finset Λ => x ∈ X),
        ‖h X‖ * (X.card : ℝ) ^ 2 *
          Real.exp (μ * Metric.diam (X : Set Λ)) ≤ ζ)
    (P S : Finset Λ) :
    (∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets P Q ∧ meets Q S),
      ‖h Q‖) ≤ ζ * ∑ p ∈ P, Real.exp (-(μ * Metric.infDist p (S : Set Λ))) ∧
    (∑ Q ∈ Finset.univ.filter (fun Q : Finset Λ => meets P Q),
      ‖h Q‖ * (Q.card : ℝ) ^ 2 * Real.exp (-(μ * setDist Q S))) ≤
      ζ * ∑ p ∈ P, Real.exp (-(μ * Metric.infDist p (S : Set Λ))) := by sorry

end LatticeHamSim.CommLR
