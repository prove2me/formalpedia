-- Prove2me | Theorems.Thm_LatticeHamSim_CommLR_eq_32
-- name    : LatticeHamSim.CommLR.eq_32
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:03:43.925562+00:00
-- url     : https://prove2.me/theorems/095137d8-ae3a-46b0-ae7a-b50ccdb7907f
-- title:
--   (32), p. 24 — convergent series over linked interaction sets
-- statement:
--   Suppose the supported Hermitian terms obey (14) for $0\le\eta\le1$. Let $X$ and $Y$ be disjoint, and let $B$ be supported on $Y$. For $k\ge1$, let $W_k(X,Y)$ be the sum over $k$ interaction sets of the product of their norms, requiring the alternating overlaps displayed in (32) and requiring the last set to meet $Y$. Then for every real $t$ there is a real sum $S$ with
--
--   $$S=\sum_{k\ge1}\frac{(2|t|)^k}{k!}\eta^{\lfloor k/2\rfloor}W_k(X,Y),\qquad C_B(X,t)\le2\|B\|S.$$
--
--   This is the series form of the recursive commutator estimate and makes the paths of interactions from $X$ to $Y$ explicit.
--
--   **Formalization Note** `HasSum` asserts that the series converges; no divergent-series default is used. Multiplication by $2\|B\|$ replaces the paper's quotient by that quantity, which would be undefined for $B=0$. The zero-based Lean summation index is $k-1$ in the displayed series. Norms are L2 operator norms.
-- source:
--   Haah, Hastings, Kothari and Low, Quantum algorithm for simulating real time evolution of lattice Hamiltonians, arXiv:1801.03922v4, p. 24, Appendix C.2, (32) and the display after (32) (“That is,”)

import Mathlib
import Definitions.Def_LatticeHamSim_CommLR_Setting
open scoped Matrix.Norms.L2Operator

namespace LatticeHamSim.CommLR

/-- The convergent linked-set series of (32), in multiplied form. -/
theorem eq_32 {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ]
    {q : ℕ} (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian)
    (hsupp : ∀ X, SupportedOn X (h X))
    (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (h14 : ∀ X Y, ‖h X * h Y - h Y * h X‖ ≤
      2 * η * ‖h X‖ * ‖h Y‖)
    (X Y : Finset Λ) (hXY : Disjoint X Y)
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hB : SupportedOn Y B) (t : ℝ) :
    ∃ S : ℝ,
      HasSum (fun k : ℕ =>
        (2 * |t|) ^ (k + 1) / ((k + 1).factorial : ℝ) *
        η ^ ((k + 1) / 2) * linkedWeight h X Y (k + 1)) S ∧
      CB h B X t ≤ 2 * ‖B‖ * S := by sorry

end LatticeHamSim.CommLR
