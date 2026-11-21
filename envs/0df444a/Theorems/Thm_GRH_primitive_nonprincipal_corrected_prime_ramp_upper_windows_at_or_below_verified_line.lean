-- Prove2me | Theorems.Thm_GRH_primitive_nonprincipal_corrected_prime_ramp_upper_windows_at_or_below_verified_line
-- name    : GRH.primitive_nonprincipal_corrected_prime_ramp_upper_windows_at_or_below_verified_line
-- status  : Open
-- author  : @marozols
-- created : 2026-11-21T03:41:55.254274+00:00
-- url     : https://prove2.me/theorems/9276b797-238b-4169-a752-b3341c64bffe
-- title:
--   Primitive nonprincipal prime-ramp windows at or below the verified line
-- statement:
--   Fix a modulus $qge 1$, a primitive nonprincipal Dirichlet character $chimod q$, and $1/2<	hetale 0.8749570698$. Let
--   $$G_chi(y)=sum_{1le nle y}Lambda(n)operatorname{Re}chi(n)(y/n-1)_+ + yoperatorname{Re}rac{L'(1,chi)}{L(1,chi)}.$$
--   There should be $delta>0$ and $Cge0$ such that for every $Xge1$ there exists $Yge X$ with
--   $$G_chi(y)le Cy^	hetaqquad(Yle yle Y^{1+delta}).$$
--   Only primitive nonprincipal characters are quantified here. A separate change-of-modulus estimate carries these windows to induced characters.
-- source:
--   Primitive-conductor restriction of https://prove2.me/theorems/edddccfa-3c07-4897-831f-46382957c69d.

import Mathlib

open Finset ArithmeticFunction Set

namespace GRH

theorem primitive_nonprincipal_corrected_prime_ramp_upper_windows_at_or_below_verified_line :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
      ∀ θ : ℝ, 1/2 < θ → θ ≤ (0.8749570698:ℝ) → ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
        ∀ X : ℝ, 1 ≤ X → ∃ Y : ℝ, X ≤ Y ∧ ∀ y ∈ Icc Y (Y^(1+δ)),
          (∑ n ∈ range (⌊y⌋₊+1), vonMangoldt n * (χ (n:ZMod q)).re * max (y/(n:ℝ)-1) 0) +
              y * (deriv χ.LFunction 1 / χ.LFunction 1).re ≤ C*y^θ := by sorry

end GRH
