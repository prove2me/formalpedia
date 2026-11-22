-- Prove2me | Theorems.Thm_MasulloGRH_intSubgroup_exists_rounding
-- name    : MasulloGRH.intSubgroup_exists_rounding
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T17:25:23.320946+00:00
-- url     : https://prove2.me/theorems/a300fec9-e3e4-462c-b3da-2d354598dfdc
-- title:
--   Subgroups of Z^r are undistorted: bounded-coefficient rounding along finitely many elements
-- statement:
--   Let $L\le\mathbb Z^r$ be a subgroup, with the sup norm. Then there are finitely many elements $b_1,\dots,b_q\in L$ and constants $K,R_0$ with the following property. Every $a\in L$ can be written as
--   $$a=\sum_{i=1}^q k_i b_i+\rho,\qquad k_i\in\mathbb Z,\quad |k_i|\le K\|a\|+1,\quad \|\rho\|\le R_0 .$$
--   In particular subgroups of $\mathbb Z^r$ are undistorted: word length is linearly bounded by the norm.
--
--   Proof: choose a maximal $\mathbb R$-linearly independent subset $\{b_i\}$ of $L\subseteq\mathbb R^r$; its real span contains $L$. The coordinate functionals of this basis are continuous, so $a=\sum c_ib_i$ with $|c_i|\le K\|a\|$. Take $k_i=\lfloor c_i\rfloor$; then $\rho=\sum(c_i-k_i)b_i$ has norm at most $\sum\|b_i\|$.
--
--   In Masullo's Appendix D this gives the polynomial growth bound of a correspondence $\beta\circ\alpha^{-1}$ between elementary groups $\mathbb R^m\times\mathbb T^n\times\mathbb Z^r\times F$. That bound is needed to transport rapid-decay functions (Lemma D.1.5.4).
-- source:
--   Standard; used in A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix D, Lemma D.1.5.4

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false

namespace MasulloGRH

theorem intSubgroup_exists_rounding
    {r : ℕ} (L : AddSubgroup (Fin r → ℤ)) :
    ∃ (ι : Type) (_ : Fintype ι) (b : ι → Fin r → ℤ) (K R₀ : ℝ), (∀ i, b i ∈ L) ∧
      ∀ a ∈ L, ∃ k : ι → ℤ, (∀ i, |(k i : ℝ)| ≤ K * ‖a‖ + 1) ∧
        ‖a - ∑ i, k i • b i‖ ≤ R₀ := by
  sorry

end MasulloGRH
