-- Prove2me | Theorems.Thm_GRH_reduced_liouville_harmonic_le_of_modulus_one
-- name    : GRH.reduced_liouville_harmonic_le_of_modulus_one
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T01:31:57.900926+00:00
-- url     : https://prove2.me/theorems/3567dbaa-4cd8-43ec-88ca-da321e585223
-- title:
--   A finite divisor sieve transfers harmonic Liouville cancellation from modulus one to every modulus
-- statement:
--   For $q\ge1$ put $H_q(U)=\sum_{1\le n\le U,\,(n,q)=1}\lambda(n)/n$. Suppose $|H_1(U)|\le C(U+1)^{\sigma-1}$ for all $U$, with $C\ge0$ and $\sigma\le1$. Then for all $U$ one has $$|H_q(U)|\le C\left(\sum_{d\mid q}|\mu(d)|d^{-\sigma}\right)(U+1)^{\sigma-1}.$$ The proof gives the exact identity $H_q(U)=\sum_{d\mid q}|\mu(d)|H_1(\lfloor U/d\rfloor)/d$. Thus cancellation in the principal coprimality filter requires only the untwisted harmonic sum.
-- source:
--   Finite Möbius inclusion–exclusion and complete multiplicativity of the Liouville function, applied to the harmonic-factor frontier 005c4a44 of the squarefree bilinear decomposition.

import Definitions.Def_GRH_SquarefreeBilinear

set_option autoImplicit false

open Finset ArithmeticFunction
open scoped BigOperators
namespace GRH

theorem reduced_liouville_harmonic_le_of_modulus_one (q : ℕ) [NeZero q] (σ C : ℝ) (hσ : σ ≤ 1) (hC : 0 ≤ C)
    (H : ∀ U : ℕ, |reducedLiouvilleHarmonic 1 U| ≤ C * ((U:ℝ)+1)^(σ-1))
    (U : ℕ) :
    |reducedLiouvilleHarmonic q U| ≤
      (C * ∑ d ∈ q.divisors, |(moebius d:ℝ)| * (d:ℝ)^(-σ)) * ((U:ℝ)+1)^(σ-1) := by sorry

end GRH
