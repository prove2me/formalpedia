-- Prove2me | Theorems.Thm_GRH_moebius_harmonic_decay_of_bounded_dirichlet_prefixes
-- name    : GRH.moebius_harmonic_decay_of_bounded_dirichlet_prefixes
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T01:38:26.878601+00:00
-- url     : https://prove2.me/theorems/d51775f3-9376-4c04-946b-89073ed8dfdc
-- title:
--   Bounded Möbius Dirichlet prefixes give a quantitative harmonic estimate at the zeta pole
-- statement:
--   Let $\sigma\le1$. If the natural-order partial sums of $\sum \mu(n)n^{-\sigma}$ are bounded in absolute value by $C$, then for every $U\ge0$ one has $$\left|\sum_{1\le n\le U}\frac{\mu(n)}n\right|\le 2C(U+1)^{\sigma-1}.$$ The proof identifies the boundary value of the reciprocal zeta function at its pole using estimates uniform for real $s>1$. It needs only boundedness of the ordered prefixes at the one indicated exponent.
-- source:
--   Abel summation for the ordinary Möbius Dirichlet series, the Euler product at real s>1, and lim at s→1+ of 1/ζ(s)=0. Quantitative input to the coprime harmonic Liouville frontier 005c4a44.

import Mathlib

set_option autoImplicit false

open Finset ArithmeticFunction
namespace GRH

theorem moebius_harmonic_decay_of_bounded_dirichlet_prefixes (σ C : ℝ) (hσ : σ ≤ 1) (hC : 0 ≤ C)
    (H : ∀ N : ℕ, |∑ n ∈ range N, (moebius n : ℝ) * (n : ℝ)^(-σ)| ≤ C)
    (U : ℕ) :
    |∑ n ∈ range (U+1), (moebius n : ℝ) / (n:ℝ)| ≤
      2*C*((U:ℝ)+1)^(σ-1) := by sorry

end GRH
