-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_uniform_cutoff_jet_bound
-- name    : HunterPDE.Sobolev.uniform_cutoff_jet_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T23:12:48.738399+00:00
-- url     : https://prove2.me/theorems/ac2ff3e6-47c1-49bb-8b12-58298ebe7ebc
-- title:
--   Uniform bounds for every finite derivative jet of expanding smooth cutoffs
-- statement:
--   Let $\chi\in C_c^\infty(\mathbb R^n)$ and $k\ge0$. There is a finite constant $C\ge0$ such that, for every integer $j\ge0$, every multi-index $|\beta|\le k$, and every $x$,
--
--   $$\left|D^\beta\left[1-\chi\left(\frac{\cdot}{j+1}\right)\right](x)\right|\le C.$$
--
--   No equality to one near zero is required. The derivative scaling formula supplies the factor $(j+1)^{-|\beta|}\le1$ for positive orders. Compact support and smoothness bound each derivative of $\chi$, and there are only finitely many orders. At order zero, use $1+\sup|\chi|$. This is useful in uniform Sobolev multiplier estimates and includes dimension zero. It is an independent open calculus obligation.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations (revised 6/18/2014), https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, Section 1.8 (multi-index derivatives), printed p. 10, and the scaled cutoff in the proof of Theorem 3.24, printed p. 59. This uniform jet bound is an elementary consequence of derivative scaling and compact support, used in the cutoff proof; not a verbatim numbered theorem.

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace

open HunterPDE.Sobolev

theorem HunterPDE.Sobolev.uniform_cutoff_jet_bound {n : ℕ} (k : ℕ)
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : IsTestFunction Set.univ χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (β : Fin n → ℕ), ∑ i, β i ≤ k →
      ∀ x, ‖iteratedPartial β (fun y => 1 - χ (((j : ℝ) + 1)⁻¹ • y)) x‖ ≤ C := by sorry
