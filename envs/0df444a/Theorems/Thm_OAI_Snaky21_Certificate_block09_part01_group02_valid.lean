-- Prove2me | Theorems.Thm_OAI_Snaky21_Certificate_block09_part01_group02_valid
-- name    : OAI.Snaky21.Certificate.block09_part01_group02_valid
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-08T13:43:30.694377+00:00
-- url     : https://prove2.me/theorems/4c57ce07-cffe-4573-872e-63539c092517
-- title:
--   21-move certificate: validity of numbered cards 600–603
-- statement:
--   The four numbered conditional Snaky claims 600 through 603 of the pinned certificate are valid, including the nested combinations in their definitions.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Snaky-in-21-Maker-moves-September-25-2026/article.pdf; Proposition 5, certificate cards 600–603.

import Theorems.Thm_OAI_Snaky21_Certificate_block09_part01_group01_valid
import Definitions.Def_Snaky21Data09
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block08_valid
import Theorems.Thm_OAI_Snaky21_Certificate_block09_part00_valid
open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate

theorem OAI.Snaky21.Certificate.block09_part01_group02_valid : Valid card_600 ∧ Valid card_601 ∧ Valid card_602 ∧ Valid card_603 ∧ True := by sorry
