-- Prove2me | Theorems.Thm_OAI_Snaky21_Certificate_catalog_correct
-- name    : OAI.Snaky21.Certificate.catalog_correct
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:55:35.938987+00:00
-- url     : https://prove2.me/theorems/c2d2bdc7-6176-4894-88ab-3a8c436643f5
-- title:
--   Proposition 5 — 728 numbered cards and the uniform height bound
-- statement:
--   The numbered-card list for the fixed 21-move Snaky certificate has exactly 728 entries, including the six bases, and every entry has positive height at most 21. This assertion concerns the explicit finite reconstruction data only; validity as game claims is proved separately.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Snaky-in-21-Maker-moves-September-25-2026/article.pdf; Proposition 5: the six bases and 722 numbered data lines, with all heights at most 21.

import Definitions.Def_Snaky21Catalog
open OAI.Snaky21.Certificate

theorem OAI.Snaky21.Certificate.catalog_correct : numberedCards.length = 728 ∧ (numberedCards.map (fun c => decide (0 < c.height ∧ c.height ≤ 21))).all id = true := by sorry
