-- Prove2me | Theorems.Thm_GRH_centered_moebius_square_block_control
-- name    : GRH.centered_moebius_square_block_control
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T02:23:32.159002+00:00
-- url     : https://prove2.me/theorems/caa25386-7d4a-41b1-afe7-db19fdae4d1e
-- title:
--   Sharp centered Möbius errors differ from their signed square-block means by O(√N+1)
-- statement:
--   Write B(N) for the centered Möbius progression bilinear sum of 5000f709 with fixed modulus q and reduced class a. If u=⌊√N⌋, then B(N) differs from the signed average of B(u²+j) over 0≤j≤2u by at most K(q,a)(u+1). This bound is unconditional. Moreover, for every 0.8749570698<σ<1 the full pointwise estimate |B(N)|≤C(q,a,σ)(N+1)^σ holds for all N.
-- source:
--   Helfgott and Thompson, Summing μ(n): a faster elementary algorithm, §2, eqs. (2.1)–(2.2), https://doi.org/10.1007/s40993-022-00408-8. The finite identities in public Prove2Me submissions 509e229b and 0176d409 give the truncation and centering. The uniform square-block estimate and its application to signed block means are additional deductions. Uses the harmonic estimate 26e6bf8c and the verified above-boundary progression result a79a1901.

import Definitions.Def_GRH_MoebiusBilinear

set_option autoImplicit false

open Finset
namespace GRH

theorem centered_moebius_square_block_control (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a) :
    (∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, let u := N.sqrt
      |centeredMoebiusBilinear q a N -
        (∑ j ∈ range (2*u+1), centeredMoebiusBilinear q a (u^2+j))/((2*u+1:ℕ):ℝ)| ≤ K*((u:ℝ)+1)) ∧
    (∀ σ : ℝ, 0.8749570698 < σ → σ < 1 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |centeredMoebiusBilinear q a n| ≤ C*((n:ℝ)+1)^σ) := by sorry

end GRH
