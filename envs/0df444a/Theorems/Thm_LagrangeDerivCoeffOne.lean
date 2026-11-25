-- Prove2me | Theorems.Thm_LagrangeDerivCoeffOne
-- name    : LagrangeDerivCoeffOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:27:53.554382+00:00
-- url     : https://prove2.me/theorems/42660b2c-7208-4bc9-a503-b8d720e8fea8
-- title:
--   Lagrange Deriv Coeff One: Lagrange Deriv Coeff One
-- statement:
--   The value of the Lagrange first-derivative coefficient at the index `i = 1`
--   and the evaluation point `1`: it equals `-2/(1 - x_1)`.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/LagrangeDerivCoeffOne.lean#L9-L81
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/LagrangeDerivCoeffOne.lean#L9-L81

module
public import Definitions.Def_PHarmonicPoly_ChebNodeTelescope
public import Definitions.Def_PHarmonicPoly_LagrangeDerivCoeffOne
public import Theorems.Thm_ChebNodeTelescope

set_option autoImplicit false
@[expose] public section
public section

theorem LagrangeDerivCoeffOne {m : ℕ} (hm : 2 ≤ m) :
    (∏ j ∈ (Finset.range (m + 1)).erase 1,
        (Polynomial.Chebyshev.node m 1 - Polynomial.Chebyshev.node m j))⁻¹ *
      (∑ t ∈ Finset.powersetCard (m - 1) ((Finset.range (m + 1)).erase 1),
        ∏ a ∈ t, (1 - Polynomial.Chebyshev.node m a))
      = -2 / (1 - Polynomial.Chebyshev.node m 1) := by sorry
