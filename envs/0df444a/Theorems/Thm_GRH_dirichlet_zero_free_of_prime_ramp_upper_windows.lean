-- Prove2me | Theorems.Thm_GRH_dirichlet_zero_free_of_prime_ramp_upper_windows
-- name    : GRH.dirichlet_zero_free_of_prime_ramp_upper_windows
-- status  : Open
-- author  : @GeorgeCoote
-- created : 2026-11-21T21:21:34.058185+00:00
-- url     : https://prove2.me/theorems/eabeaaa2-3c8c-4f76-a62b-d3512cab57b7
-- title:
--   Dirichlet nonvanishing from one-sided prime-ramp bounds on cofinal windows
-- statement:
--   Let $\chi$ be a complex Dirichlet character modulo $N$, where $N=1$ or $\chi$ is nonprincipal. Define the corrected prime ramp as
--   $$
--   G_\chi(y)=\sum_{1\le n\le y}\Lambda(n)\operatorname{Re}\chi(n)\max(y/n-1,0)+R_\chi(y).
--   $$
--   For $N=1$ use $R_\chi(y)=-y(\log y-1-\gamma)$, where $\gamma$ is the Euler–Mascheroni constant. For a nonprincipal character use
--   $$
--   R_\chi(y)=y\operatorname{Re}\frac{L'(1,\chi)}{L(1,\chi)}.
--   $$
--
--   Fix $0<\theta<1$. Suppose there are $\delta>0$ and $C\ge0$ such that arbitrarily large $Y$ satisfy
--   $$
--   G_\chi(y)\le C y^\theta \qquad (Y\le y\le Y^{1+\delta}).
--   $$
--   Then $L(s,\chi)\ne0$ whenever $\theta<\operatorname{Re}s<1$.
-- source:
--   Singleton family with weight 1 in Deduction.zeroFree_of_rpow_window, Levent Alpöge with Claude, 20 November 2026 Lean release, https://github.com/leanprover-community/riemann-hypothesis/blob/main/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ZeroFreeOfRpowWindow.lean#L10-L13. The ramps are Deduction.G and Deduction.Gchi in CharFamily.lean.

import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

set_option autoImplicit false

namespace GRH

theorem dirichlet_zero_free_of_prime_ramp_upper_windows
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : N = 1 ∨ χ ≠ 1) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hwindows : ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ X : ℝ, 1 ≤ X → ∃ Y : ℝ, X ≤ Y ∧
        ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)),
          (if N = 1 then
            (∑ n ∈ Finset.range (⌊y⌋₊ + 1),
              ArithmeticFunction.vonMangoldt n * max (y / (n : ℝ) - 1) 0) -
                y * (Real.log y - 1 - Real.eulerMascheroniConstant)
          else
            (∑ n ∈ Finset.range (⌊y⌋₊ + 1),
              ArithmeticFunction.vonMangoldt n * (χ (n : ZMod N)).re *
                max (y / (n : ℝ) - 1) 0) +
                  y * (deriv χ.LFunction 1 / χ.LFunction 1).re) ≤ C * y ^ θ) :
    ∀ s : ℂ, θ < s.re → s.re < 1 → χ.LFunction s ≠ 0 := by
  sorry

end GRH
