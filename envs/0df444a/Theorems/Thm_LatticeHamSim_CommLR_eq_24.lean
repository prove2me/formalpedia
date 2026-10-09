-- Prove2me | Theorems.Thm_LatticeHamSim_CommLR_eq_24
-- name    : LatticeHamSim.CommLR.eq_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:03:43.016985+00:00
-- url     : https://prove2.me/theorems/76cef9c4-c5e3-4cec-9355-a95584723ebc
-- title:
--   (24), p. 23 — integral inequality for C_B
-- statement:
--   For a finite Hamiltonian $H=\sum_Zh_Z$ whose Hermitian terms are supported on $Z$, fix an operator $B$ supported on $Y$. For any $X$ and $t\ge0$,
--
--   $$C_B(X,t)\le C_B(X,0)+\sum_{Z:Z\sim X}2\int_0^t D_B(Z,s)\,ds.$$
--
--   This inequality relates the commutator of an arbitrary local observable to the evolved interaction terms meeting its initial support. It is the first integral estimate in the chain leading to Lemma 12.
--
--   **Formalization Note** The paper prints $|t|$ as upper limit; the forward-time derivation on page 23 uses $D_B(Z,s)$ and this item states that direction for $t\ge0$. The integrands are continuous finite-matrix expressions, so the integrals are genuine. The norm is the L2 operator norm.
-- source:
--   Haah, Hastings, Kothari and Low, Quantum algorithm for simulating real time evolution of lattice Hamiltonians, arXiv:1801.03922v4, p. 23, Appendix C.2, (24)

import Mathlib
import Definitions.Def_LatticeHamSim_CommLR_Setting
open scoped Matrix.Norms.L2Operator

namespace LatticeHamSim.CommLR

attribute [local instance] Classical.propDecidable

/-- Integral inequality (24) for nonnegative time. -/
theorem eq_24 {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ]
    {q : ℕ} (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian)
    (hsupp : ∀ X, SupportedOn X (h X))
    (Y : Finset Λ) (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hB : SupportedOn Y B) (X : Finset Λ) (t : ℝ) (ht : 0 ≤ t) :
    CB h B X t ≤ CB h B X 0 +
      ∑ Z ∈ Finset.univ.filter (fun Z : Finset Λ => meets Z X),
        2 * ∫ s in (0:ℝ)..t, DB h B Z s := by sorry

end LatticeHamSim.CommLR
