-- Prove2me | Theorems.Thm_IntegerMatrixMortality_FixedImage_fixed_machine_undecidable
-- name    : IntegerMatrixMortality.FixedImage.fixed_machine_undecidable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:34:08.81305+00:00
-- url     : https://prove2.me/theorems/5b96ab23-8ca1-4d5b-954b-2c6e394ca020
-- title:
--   Proposition 4.1 — Undecidability of the fixed machine
-- statement:
--   Let U be the fixed concrete two-counter machine obtained from the four state identifications in Table 2. No total computable Boolean function f on natural inputs satisfies
--
--   $$f(\rho)=\mathrm{true}\iff\operatorname{Halts}_U(1,\rho,0)\qquad\text{for all }\rho\in\mathbb N.$$
--
--   This is the unconditional source of undecidability; universality is a proof obligation, never an assumption on a machine parameter.
--
--   Differences from the source:
--   - encoding: the fixed source machine and reversed program → the full 278-row table, representative quotient, and named reversed program P; reason: the definitions are the source construction, without a universality or simulation premise
-- source:
--   Thanin Quartz, Ivan O. Shevchenko, Hans De Sterck, Jun Liu, STOC 2027 submission #1062 (October 2026), Proposition 4.1, PDF p. 7 / printed p. 5

import Definitions.Def_IntegerMatrixMortality_FixedImage_ScanInterfaces

set_option autoImplicit false

namespace IntegerMatrixMortality.FixedImage

theorem fixed_machine_undecidable
    : ¬ ∃ f : ℕ → Bool, Computable f ∧
      ∀ ρ : ℕ, f ρ = true ↔ machineHalts U (1,ρ,0) := by sorry

end IntegerMatrixMortality.FixedImage
