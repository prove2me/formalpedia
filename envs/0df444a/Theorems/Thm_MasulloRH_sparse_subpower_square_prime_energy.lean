-- Prove2me | Theorems.Thm_MasulloRH_sparse_subpower_square_prime_energy
-- name    : MasulloRH.sparse_subpower_square_prime_energy
-- status  : Open
-- author  : @marozols
-- created : 2026-11-21T03:50:19.837527+00:00
-- url     : https://prove2.me/theorems/c62eb880-c622-4728-bcd9-a5fca406400e
-- title:
--   Eventually subpower prime energies at doubly exponential arithmetic cutoffs
-- statement:
--   For all sufficiently large j, the square-sampled finite prime energy E(D_j) at D_j=2^(2^j) is at most D_j^(1/(j+1)). This single growing allowance is checked at sparse finite cutoffs. E(N) is the sum over k=4,...,N+3 of G(k²)²/[k³(1+log k)²] for the corrected von Mangoldt ramp.
-- source:
--   Open finite-arithmetic input for b41359f9. It relaxes the all-cutoff constant 81 to an unbounded allowance at doubly exponential cutoffs. The converse uses the actual continuous prime-ramp energy and the Dirichlet series of the nonnegative sampled coefficients.

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib
set_option autoImplicit false

open Finset ArithmeticFunction MeasureTheory Set
namespace MasulloRH

theorem sparse_subpower_square_prime_energy :
    let G (x : ℝ) := (∑ n ∈ range (⌊x⌋₊+1),vonMangoldt n*max (x/(n:ℝ)-1) 0) -
      x*(Real.log x-1-Real.eulerMascheroniConstant)
    let E (N : ℕ) := ∑ n ∈ range N, let k := (n:ℝ)+4; (G (k^2))^2/(k^3*(1+Real.log k)^2)
    ∃ J : ℕ,∀ j ≥ J, let D := (2:ℕ)^(2^j)
      E D ≤ (D:ℝ)^(1/((j:ℝ)+1)) := by sorry

end MasulloRH
