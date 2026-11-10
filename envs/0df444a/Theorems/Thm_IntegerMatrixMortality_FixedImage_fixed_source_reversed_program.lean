-- Prove2me | Theorems.Thm_IntegerMatrixMortality_FixedImage_fixed_source_reversed_program
-- name    : IntegerMatrixMortality.FixedImage.fixed_source_reversed_program
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:33:56.23107+00:00
-- url     : https://prove2.me/theorems/e6aadeef-848e-431a-8d40-c81c2febc3c0
-- title:
--   Theorem 4.3 — Fixed-source reversed program
-- statement:
--   Let P be the concrete finite reversed program built from U by the prime-exponent simulation, cleanup at state 278, and exact reversal of the partial maps. Every instruction of P is well formed and belongs to Table 1. For every natural input ρ,
--
--   $$(278,0)\longrightarrow_P^*(1,2^\rho-1)\iff\operatorname{Halts}_U(1,\rho,0).$$
--
--   The source is fixed and the target alone depends on ρ. All finite paths, including the empty one, are included.
--
--   Differences from the source:
--   - encoding: the fixed source machine and reversed program → the full 278-row table, representative quotient, and named reversed program P; reason: the definitions are the source construction, without a universality or simulation premise
-- source:
--   Thanin Quartz, Ivan O. Shevchenko, Hans De Sterck, Jun Liu, STOC 2027 submission #1062 (October 2026), Theorem 4.3, PDF p. 8 / printed p. 6

import Definitions.Def_IntegerMatrixMortality_FixedImage_ScanInterfaces

set_option autoImplicit false

namespace IntegerMatrixMortality.FixedImage

theorem fixed_source_reversed_program
    : (∀ e ∈ fixedInstructionEdges, WellFormedInstruction e.instruction) ∧
      ∀ ρ : ℕ, programReach P (278,0) (1,2^ρ-1) ↔ machineHalts U (1,ρ,0) := by sorry

end IntegerMatrixMortality.FixedImage
