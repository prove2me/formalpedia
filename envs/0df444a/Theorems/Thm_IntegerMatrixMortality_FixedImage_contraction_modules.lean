-- Prove2me | Theorems.Thm_IntegerMatrixMortality_FixedImage_contraction_modules
-- name    : IntegerMatrixMortality.FixedImage.contraction_modules
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T14:34:19.273268+00:00
-- url     : https://prove2.me/theorems/6a736939-5bda-4d45-8f30-bf6bc58c576f
-- title:
--   Corollary D.5 — Contraction modules
-- statement:
--   The assembled contraction graphs satisfy all three requirements of §5.3 for every prime p≥7, with exact partial updates
--
--   $$z_{5a+4}\longmapsto z_{2a+1},\qquad z_{5a+4}\longmapsto z_{3a+2}.$$
--
--   They have respectively 30 and 32 listed generators. The first combines two-block removal with two-scan recovery; the second combines one-block removal with three-scan recovery. Every valid unfinished prefix, including an incorrect guess at a private join, obeys the residue requirement.
--
--   Differences from the source:
--   - encoding: a concrete finite source module with private phases → the corresponding named finite edge list, with all three requirements asserted; reason: local labels are renamed privately for each occurrence, including coincident program boundaries
-- source:
--   Thanin Quartz, Ivan O. Shevchenko, Hans De Sterck, Jun Liu, STOC 2027 submission #1062 (October 2026), Corollary D.5, PDF p. 29 / printed p. 27

import Definitions.Def_IntegerMatrixMortality_FixedImage_ScanInterfaces

set_option autoImplicit false

namespace IntegerMatrixMortality.FixedImage

theorem contraction_modules
    : ModuleRequirements (contractionModule 2) (instructionUpdate .con2) ∧
      ModuleRequirements (contractionModule 3) (instructionUpdate .con3) ∧
      (contractionModule 2).edges.length = 30 ∧
      (contractionModule 3).edges.length = 32 := by sorry

end IntegerMatrixMortality.FixedImage
