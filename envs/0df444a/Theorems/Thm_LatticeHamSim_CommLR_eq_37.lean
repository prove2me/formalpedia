-- Prove2me | Theorems.Thm_LatticeHamSim_CommLR_eq_37
-- name    : LatticeHamSim.CommLR.eq_37
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:05:41.068009+00:00
-- url     : https://prove2.me/theorems/2829447f-b288-4916-9089-b2a0ff80ce38
-- title:
--   (37), p. 25 — bound on each linked interaction series term
-- statement:
--   Let $0\le\eta\le1$ be the parameter of (14), and assume the weighted decay condition (15) with $\zeta,\mu>0$. For any sets $X,Y$, real time $t$, and integer $k\ge1$, the $k$th linked term of (32) obeys
--
--   $$\frac{(2|t|)^k}{k!}\eta^{\lfloor k/2\rfloor}W_k(X,Y)\le\frac{(2|t|)^k}{k!}\eta^{\lfloor k/2\rfloor}2^{\lfloor(k-1)/2\rfloor}\zeta^k\sum_{x\in X}e^{-\mu\operatorname{dist}(x,Y)}.$$
--
--   This is the $k$th-line estimate (37) of the paper. Its factor $2^{\lfloor(k-1)/2\rfloor}$ is kept exactly.
--
--   **Formalization Note** The statement retains the common time and $\eta$ factor, including its zero cases. The assumption $k\ge1$ avoids natural-number subtraction at zero. Norms are L2 operator norms.
-- source:
--   Haah, Hastings, Kothari and Low, Quantum algorithm for simulating real time evolution of lattice Hamiltonians, arXiv:1801.03922v4, p. 25, Appendix C.3, (37)

import Mathlib
import Definitions.Def_LatticeHamSim_CommLR_Setting
open scoped Matrix.Norms.L2Operator

namespace LatticeHamSim.CommLR

/-- The bound on the k-th line of the linked-set series in (37). -/
theorem eq_37 {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ]
    {q : ℕ} (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (η ζ μ : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hζ : 0 < ζ) (hμ : 0 < μ)
    (h15 : ∀ x : Λ,
      ∑ Z ∈ Finset.univ.filter (fun Z : Finset Λ => x ∈ Z),
        ‖h Z‖ * (Z.card : ℝ) ^ 2 *
          Real.exp (μ * Metric.diam (Z : Set Λ)) ≤ ζ)
    (X Y : Finset Λ) (t : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    (2 * |t|) ^ k / (k.factorial : ℝ) * η ^ (k / 2) *
      linkedWeight h X Y k ≤
      (2 * |t|) ^ k / (k.factorial : ℝ) * η ^ (k / 2) *
      2 ^ ((k - 1) / 2) * ζ ^ k *
        ∑ x ∈ X, Real.exp (-(μ * Metric.infDist x (Y : Set Λ))) := by sorry

end LatticeHamSim.CommLR
