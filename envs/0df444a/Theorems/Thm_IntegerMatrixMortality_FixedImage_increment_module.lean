-- Prove2me | Theorems.Thm_IntegerMatrixMortality_FixedImage_increment_module
-- name    : IntegerMatrixMortality.FixedImage.increment_module
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:34:11.664448+00:00
-- url     : https://prove2.me/theorems/ac69c0cf-a66e-4ccc-81a7-e667727ad9e1
-- title:
--   Proposition C.1 — Increment module
-- statement:
--   The four-generator graph (C.1) satisfies all three module requirements of §5.3 for every prime p≥7. For every natural input n it has a valid completing path, and every such completion gives exactly
--
--   $$z_n\longmapsto z_{n+1}.$$
--
--   All valid prefixes, including the direct marker exit at n=0, have residues in Δ. The finite effective graph has exactly four listed generators.
--
--   Differences from the source:
--   - encoding: a concrete finite source module with private phases → the corresponding named finite edge list, with all three requirements asserted; reason: local labels are renamed privately for each occurrence, including coincident program boundaries
-- source:
--   Thanin Quartz, Ivan O. Shevchenko, Hans De Sterck, Jun Liu, STOC 2027 submission #1062 (October 2026), Proposition C.1, PDF p. 20 / printed p. 18

import Definitions.Def_IntegerMatrixMortality_FixedImage_ScanInterfaces

set_option autoImplicit false

namespace IntegerMatrixMortality.FixedImage

theorem increment_module
    : ModuleRequirements incrementModule (instructionUpdate .inc) ∧
      incrementModule.edges.length = 4 := by sorry

end IntegerMatrixMortality.FixedImage
