-- Prove2me | Theorems.Thm_LatticeHamSim_CommLR_eq_27
-- name    : LatticeHamSim.CommLR.eq_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:04:01.830437+00:00
-- url     : https://prove2.me/theorems/48600de4-3ab6-4bb2-bca5-5d922606bacc
-- title:
--   (27), p. 23 — integral inequality for D_B under (14)
-- statement:
--   Let $h_X$ be supported Hermitian interaction terms satisfying $\|[h_X,h_Z]\|\le2\eta\|h_X\|\|h_Z\|$ for a nonnegative $\eta$. Fix $B$ supported on $Y$. For every $X$ and $t\ge0$,
--
--   $$D_B(X,t)\le D_B(X,0)+\sum_{Z:Z\sim X}2\eta\int_0^t\|h_Z\|\|h_X\|C_B(Z\cup X,s)\,ds.$$
--
--   The estimate carries the small commutator parameter into the evolution of one interaction term. Together with (24), it is an input to the linked-set series.
--
--   **Formalization Note** The forward-time restriction makes the integral's argument agree with the derivation on page 23. All matrix norms are L2 operator norms; the integral is a finite interval integral of continuous functions.
-- source:
--   Haah, Hastings, Kothari and Low, Quantum algorithm for simulating real time evolution of lattice Hamiltonians, arXiv:1801.03922v4, p. 23, Appendix C.2, (26)–(27)

import Mathlib
import Definitions.Def_LatticeHamSim_CommLR_Setting
open scoped Matrix.Norms.L2Operator

namespace LatticeHamSim.CommLR

attribute [local instance] Classical.propDecidable

/-- Integral inequality (27) under the small-commutator assumption (14). -/
theorem eq_27 {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ]
    {q : ℕ} (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian)
    (hsupp : ∀ X, SupportedOn X (h X))
    (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (h14 : ∀ X Y, ‖h X * h Y - h Y * h X‖ ≤
      2 * η * ‖h X‖ * ‖h Y‖)
    (Y : Finset Λ) (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hB : SupportedOn Y B) (X : Finset Λ) (t : ℝ) (ht : 0 ≤ t) :
    DB h B X t ≤ DB h B X 0 +
      ∑ Z ∈ Finset.univ.filter (fun Z : Finset Λ => meets Z X),
        2 * η * ∫ s in (0:ℝ)..t,
          ‖h Z‖ * ‖h X‖ * CB h B (Z ∪ X) s := by sorry

end LatticeHamSim.CommLR
