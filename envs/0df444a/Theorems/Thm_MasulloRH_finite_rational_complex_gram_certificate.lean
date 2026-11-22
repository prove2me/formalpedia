-- Prove2me | Theorems.Thm_MasulloRH_finite_rational_complex_gram_certificate
-- name    : MasulloRH.finite_rational_complex_gram_certificate
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T15:01:14.027228+00:00
-- url     : https://prove2.me/theorems/9abc9762-4566-4482-8208-1226da0ef729
-- title:
--   Rational complex matrix certificates preserve strict quadratic-form bounds
-- statement:
--   Let $I$ be a finite index set, $d:I\to\mathbb C$ a coefficient vector, $G:I\times I\to\mathbb C$ an arbitrary complex matrix, and $b\in\mathbb R$. Define
--
--   $$
--   g=\operatorname{Re}\sum_{i,j\in I}\overline{d_i}d_jG_{ij},\qquad
--   S=\sum_{i\in I}(|\operatorname{Re}d_i|+|\operatorname{Im}d_i|).
--   $$
--
--   If $g<b$, then there are rational pairs $R_{ij}=(r_{ij},s_{ij})\in\mathbb Q^2$ and a rational number $\eta\ge0$ such that, writing $Q_{ij}=r_{ij}+\mathrm{i}s_{ij}$,
--
--   $$
--   |G_{ij}-Q_{ij}|\le\eta\quad\text{for every }i,j\in I,
--   \qquad
--   \operatorname{Re}\sum_{i,j\in I}\overline{d_i}d_jQ_{ij}+\eta S^2<b.
--   $$
--
--   This converts a strict bound on an exact finite quadratic form into a finite rational matrix approximation with an explicit allowance for entrywise error. No Hermitian symmetry or positivity assumption on $G$ is required. When the real and imaginary parts of $d_i$ and the threshold $b$ are rational, the displayed certificate inequality involves only rational quantities.
--
--   **Formalization Note.** Rational complex entries are represented by pairs of rationals. The theorem applies to every finite type, including the empty type.
-- source:
--   Elementary finite-dimensional rounding lemma formalized for this contribution, supporting MasulloRH.cofinal_rational_theta_gram_interval_tables, https://prove2.me/theorems/7f59c68d-29e6-404c-a754-27288c412b6c . The source target fixes the entrywise-error certificate and coefficient bound used here. This is original supporting formalization, not a theorem claimed to be extracted from Masullo, The Music of the Primes. Its proof uses rational density and the triangle inequality.

import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option autoImplicit false
open scoped BigOperators ComplexConjugate

theorem MasulloRH.finite_rational_complex_gram_certificate {ι : Type*} [Fintype ι]
    (d : ι → ℂ) (G : ι → ι → ℂ) (b : ℝ)
    (hgap : (∑ i, ∑ j, conj (d i) * d j * G i j).re < b) :
    ∃ (R : ι → ι → ℚ × ℚ) (η : ℚ), 0 ≤ η ∧
      (∀ i j, ‖G i j - (((R i j).1 : ℂ) + ((R i j).2 : ℂ) * Complex.I)‖ ≤ (η : ℝ)) ∧
      (∑ i, ∑ j, conj (d i) * d j *
        (((R i j).1 : ℂ) + ((R i j).2 : ℂ) * Complex.I)).re +
        (η : ℝ) * (∑ i, (|(d i).re| + |(d i).im|)) ^ 2 < b := by sorry
