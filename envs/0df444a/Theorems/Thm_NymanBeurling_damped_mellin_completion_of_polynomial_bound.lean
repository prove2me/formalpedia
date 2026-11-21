-- Prove2me | Theorems.Thm_NymanBeurling_damped_mellin_completion_of_polynomial_bound
-- name    : NymanBeurling.damped_mellin_completion_of_polynomial_bound
-- status  : Proved
-- author  : @pragyan
-- created : 2026-11-21T04:04:49.364269+00:00
-- url     : https://prove2.me/theorems/5c32d1bb-7a5a-48b3-b6f5-6953c1dfe66f
-- title:
--   Fixed-damping Mellin completion from uniform Möbius polynomial bounds
-- statement:
--   Assume the uniform Möbius Dirichlet-polynomial bound stated in `MoebiusPolynomialBoundaryBound`. For each fixed $0<\varepsilon<1/2$, the finite residuals $R_{N,\varepsilon}$ then converge to the explicit profile $P_\varepsilon$ in the weighted sequence norm with weights $1/[m(m+1)]$, uniformly over finite coordinate prefixes. Moreover the profile has finite weighted energy and the exact identity
--   $$\int_{\mathbb R}|F_\varepsilon(t)|^2\,dt
--   =2\pi\sum_{m\ge1}\frac{P_\varepsilon(m)^2}{m(m+1)}$$
--   holds, with an integrable left-hand side. Here $F_\varepsilon$ is the explicit shifted-zeta spectral residual defined in `DampedMellinFrontiers`.
--
--   This is an unconditional implication with an explicit analytic hypothesis, currently an open formalization obligation. It separates the normal-family, dominated-convergence, and Mellin completion arguments from the unproved arithmetic bound. It does not assert that its hypothesis is known. The existing proved finite remainder Mellin--Plancherel identity is intended as its finite-dimensional starting point.
-- source:
--   B. Bagchi, On Nyman, Beurling and Baez-Duarte's Hilbert space reformulation of the Riemann hypothesis, https://arxiv.org/pdf/math/0607733 . Theorem 2 proof pp.140–141 (first damped limit), and Theorem 1 proof p.145 (discrete weighted-sequence identification). Derived conditional transfer statement: normal families identify the Dirichlet-series limit, unconditional critical-line zeta growth gives domination, and completion of the finite Mellin isometry gives the displayed identity. The source assumes RH to obtain the polynomial hypothesis; the implication here instead takes that hypothesis explicitly. Existing platform base: https://prove2.me/theorems/516ee0b8-961c-4204-8d6b-cca1ccbeedac .

import Definitions.Def_NymanBeurling_DampedMellinFrontiers
import Definitions.Def_NymanBeurling_DampedResidualLimits
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false
open scoped BigOperators
open MeasureTheory

theorem NymanBeurling.damped_mellin_completion_of_polynomial_bound
    (hpoly : NymanBeurling.MoebiusPolynomialBoundaryBound) :
    (∀ ε : ℝ, 0 < ε → ε < 1/2 → ∀ δ : ℝ, 0 < δ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ H : ℕ,
        (∑ n ∈ Finset.range H,
          (NymanBeurling.dampedResidualFinite N ε (n+1) -
            NymanBeurling.dampedResidualProfile ε (n+1))^2 /
              ((n+1 : ℝ)*(n+2 : ℝ))) < δ) ∧
    (∀ ε : ℝ, 0 < ε → ε < 1/2 →
      Summable (fun n : ℕ => (NymanBeurling.dampedResidualProfile ε (n+1))^2 /
        ((n+1 : ℝ)*(n+2 : ℝ))) ∧
      Integrable (fun t : ℝ => ‖NymanBeurling.dampedSpectralResidual ε t‖^2) ∧
      (∫ t : ℝ, ‖NymanBeurling.dampedSpectralResidual ε t‖^2) =
        2*Real.pi * ∑' n : ℕ, (NymanBeurling.dampedResidualProfile ε (n+1))^2 /
          ((n+1 : ℝ)*(n+2 : ℝ))) := by sorry
