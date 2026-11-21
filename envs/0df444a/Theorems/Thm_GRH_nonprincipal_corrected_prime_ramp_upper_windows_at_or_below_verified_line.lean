-- Prove2me | Theorems.Thm_GRH_nonprincipal_corrected_prime_ramp_upper_windows_at_or_below_verified_line
-- name    : GRH.nonprincipal_corrected_prime_ramp_upper_windows_at_or_below_verified_line
-- status  : Open
-- author  : @marozols
-- created : 2026-11-21T03:24:03.544748+00:00
-- url     : https://prove2.me/theorems/edddccfa-3c07-4897-831f-46382957c69d
-- title:
--   Nonprincipal Dirichlet prime-ramp windows at or below the verified line
-- statement:
--   Fix a modulus $q\ge1$, a nonprincipal Dirichlet character $\chi\bmod q$, and a real number $1/2<\theta\le 0.8749570698$. Define the corrected real prime ramp by
--   $$G_\chi(y)=\sum_{1\le n\le y}\Lambda(n)\operatorname{Re}\chi(n)\,(y/n-1)_+ + y\operatorname{Re}\frac{L'(1,\chi)}{L(1,\chi)}.$$
--   The proposed estimate asserts that there are $\delta>0$ and $C\ge0$ such that every $X\ge1$ admits $Y\ge X$ with $G_\chi(y)\le Cy^\theta$ for every $y\in[Y,Y^{1+\delta}]$. The correction removes the pole at $s=1$ in the ramp transform. Only an upper bound on these relative windows is required. This is the remaining range for the nonprincipal arithmetic input in the primitive Dirichlet reduction. Above the cutoff, the formally verified Dirichlet zero-free region allows an absolutely convergent contour shift and a two-sided estimate at every scale.
-- source:
--   Levent Alpöge, 20 November 2026, https://alpo.ge/remark.pdf; released module Development.AutomorphicArithmetic.DedekindLFunctions.CharFamily, `Gchi`; analytic upper-window criterion in LandauTheorems.ZeroFreeOfRpowWindow.

import Mathlib

open Finset ArithmeticFunction Set

namespace GRH

theorem nonprincipal_corrected_prime_ramp_upper_windows_at_or_below_verified_line :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ θ : ℝ, 1/2 < θ → θ ≤ (0.8749570698:ℝ) → ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
        ∀ X : ℝ, 1 ≤ X → ∃ Y : ℝ, X ≤ Y ∧ ∀ y ∈ Icc Y (Y^(1+δ)),
          (∑ n ∈ range (⌊y⌋₊+1), vonMangoldt n * (χ (n:ZMod q)).re * max (y/(n:ℝ)-1) 0) +
              y * (deriv χ.LFunction 1 / χ.LFunction 1).re ≤ C*y^θ := by sorry

end GRH
