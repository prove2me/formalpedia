-- Prove2me | Theorems.Thm_HGASUndecidable_Main_validCode_computablePred
-- name    : HGASUndecidable.Main.validCode_computablePred
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:23:17.098218+00:00
-- url     : https://prove2.me/theorems/a0d4643a-7283-434c-9346-8df302174a27
-- title:
--   Validity of finite polynomial field codes is computable
-- statement:
--   The predicate `ValidCode` on finite rational polynomial codes is computable. Its test consists of natural-number comparisons together with checking every exponent list for sortedness, duplicate-freeness, bounded coordinates, and the required total degree, so it is decided by a finite traversal of the input list.
-- source:
--   Paper #1477, fixed finite encoding and degree/homogeneity format checks described before Theorem 1.1 (printed pp. 1–3/PDF 3–5), in the precise `ValidCode` form adopted by the mission's Codes definition. This is a finite-format obligation for Theorem 2.1 (printed pp. 11–12/PDF 13–14).

import Definitions.Def_HGASUndecidable_Main_PaddingCodes

theorem HGASUndecidable.Main.validCode_computablePred :
    ComputablePred HGASUndecidable.Main.ValidCode := by sorry
