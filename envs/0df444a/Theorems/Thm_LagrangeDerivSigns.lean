-- Prove2me | Theorems.Thm_LagrangeDerivSigns
-- name    : LagrangeDerivSigns
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T15:13:36.020918+00:00
-- url     : https://prove2.me/theorems/5400e5fb-a577-4efb-aef4-5bd2d8b612be
-- title:
--   Lagrange Deriv Signs: Lagrange Deriv Signs
-- statement:
--   Sign of the Lagrange iterated-derivative coefficients at the Chebyshev
--   extremal nodes: `(-1)^i * c i ≥ 0`.
--
--   Source: https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/LagrangeDerivSigns.lean#L9-L41
-- source:
--   https://github.com/na0b/pharmonicpoly-lean/blob/df7300b4503a05e91ccf27d17867a227b263850b/PHarmonicPoly/LagrangeDerivSigns.lean#L9-L41

module
public import Definitions.Def_PHarmonicPoly_Preamble
public import Definitions.Def_PHarmonicPoly_LagrangeDerivSigns
set_option autoImplicit false
@[expose] public section
public section

theorem LagrangeDerivSigns (m i : ℕ) (hi : i ≤ m) (k : ℕ) :
    0 ≤ (-1 : ℝ) ^ i *
      ((∏ j ∈ (Finset.range (m + 1)).erase i,
            (Polynomial.Chebyshev.node m i - Polynomial.Chebyshev.node m j))⁻¹ *
        ∑ t ∈ Finset.powersetCard k ((Finset.range (m + 1)).erase i),
          ∏ a ∈ t, (1 - Polynomial.Chebyshev.node m a)) := by sorry
