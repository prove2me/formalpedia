-- Prove2me | Theorems.Thm_IntegerMatrixMortality_FixedImage_all_instruction_modules
-- name    : IntegerMatrixMortality.FixedImage.all_instruction_modules
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:34:11.150094+00:00
-- url     : https://prove2.me/theorems/ef02afa7-bc66-4b64-acca-9fefbca9520c
-- title:
--   Proposition 6.1 — All instruction modules
-- statement:
--   For every well-formed instruction i in Table 1, its concrete source-table graph satisfies the three module requirements:
--
--   $$\text{valid-prefix residues in }\Delta;\quad\text{exact domain and unary output};\quad\text{effective fixed formulas}.$$
--
--   The same finite graph and formulas work for every prime p≥7 and every numerical input. Tests range over all d≥1 and all A⊆{0,…,d−1}. This asserts correctness of the actual constructions, with no supplied simulation certificate.
--
--   Differences from the source:
--   - encoding: a concrete finite source module with private phases → the corresponding named finite edge list, with all three requirements asserted; reason: local labels are renamed privately for each occurrence, including coincident program boundaries
-- source:
--   Thanin Quartz, Ivan O. Shevchenko, Hans De Sterck, Jun Liu, STOC 2027 submission #1062 (October 2026), Proposition 6.1, PDF p. 14 / printed p. 12

import Definitions.Def_IntegerMatrixMortality_FixedImage_ScanInterfaces

set_option autoImplicit false

namespace IntegerMatrixMortality.FixedImage

theorem all_instruction_modules
    (i : ArithmeticInstruction) (hi : WellFormedInstruction i) :
      ModuleRequirements (concreteModule i) (instructionUpdate i) := by sorry

end IntegerMatrixMortality.FixedImage
