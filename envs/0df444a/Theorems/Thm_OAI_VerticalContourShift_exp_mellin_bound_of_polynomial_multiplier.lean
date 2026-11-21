-- Prove2me | Theorems.Thm_OAI_VerticalContourShift_exp_mellin_bound_of_polynomial_multiplier
-- name    : OAI.VerticalContourShift.exp_mellin_bound_of_polynomial_multiplier
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T00:22:38.866604+00:00
-- url     : https://prove2.me/theorems/b1ac5766-5e33-4891-83ad-96e705513fd7
-- title:
--   Power bound for an inverse Mellin integral with a polynomially bounded multiplier
-- statement:
--   Fix real numbers $0<a\le b$, a complex constant $k$, and a multiplier $R$ complex differentiable at every point of the closed vertical strip $a\le\Re z\le b$. Suppose there are $A,M\ge0$ such that on the strip
--   $$
--   |R(z)|\le A(1+|\Im z|)^M.
--   $$
--   Suppose also that for every natural number $m$ there is $B_m>0$ such that throughout the strip
--   $$
--   |\Gamma(z)|\le B_m(1+|\Im z|)^{-m}.
--   $$
--   If $S:[1,\infty)\to\mathbb C$ is given on the right edge by
--   $$
--   S(D)=k\int_{\mathbb R}\Gamma(b+it)D^{b+it}R(b+it)\,dt,
--   $$
--   then there is $K>0$ such that $|S(D)|\le K D^a$ for every $D\ge1$. Both edge integrals converge absolutely. The assertion specializes to the inverse of a nonprincipal Dirichlet $L$-function on the strip from $9/10$ to $2$, once its holomorphy, growth bound, and inversion identity are supplied.
-- source:
--   Mellin inversion and contour displacement; cf. NIST Digital Library of Mathematical Functions, §2.5(i), equations (2.5.2), (2.5.6), https://dlmf.nist.gov/2.5.i. This conditional estimate is the positive-strip specialization for the exponential kernel with explicitly quantified decay.

import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option autoImplicit false
open MeasureTheory Filter Set
open scoped Topology

theorem OAI.VerticalContourShift.exp_mellin_bound_of_polynomial_multiplier (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (R : ℂ → ℂ)
    (S : ℝ → ℂ) (k : ℂ)
    (hR : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → DifferentiableAt ℂ R z)
    (hpoly : ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖R z‖ ≤ C * (1 + |z.im|) ^ M)
    (hgamma : ∀ m : ℕ, ∃ B : ℝ, 0 < B ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖Complex.Gamma z‖ ≤ B / (1 + |z.im|) ^ m)
    (hinv : ∀ D : ℝ, 1 ≤ D → S D = k * ∫ t : ℝ,
      Complex.Gamma ((b : ℂ) + t * Complex.I) * (D : ℂ) ^ ((b : ℂ) + t * Complex.I) *
        R ((b : ℂ) + t * Complex.I)) :
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℝ, 1 ≤ D → ‖S D‖ ≤ C * D ^ a := by sorry
