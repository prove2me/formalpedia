-- Prove2me | Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
-- name    : OAI.Snaky21.Certificate.block01_valid
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-08T08:18:40.447534+00:00
-- url     : https://prove2.me/theorems/8150bd6c-c2f6-45ab-98a2-c72b01d8cf96
-- title:
--   21-move certificate: validity of numbered cards 64–127
-- statement:
--   Every numbered card from 64 through 127 of the fixed 21-move certificate is a valid conditional claim. The required set, envelope and height are the literal finite reconstruction of the printed data, including every nested combination. Every actual combination equation is checked by Lean kernel reduction, and the game meaning follows from the conditional-claim calculus and earlier numbered cards.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Snaky-in-21-Maker-moves-September-25-2026/article.pdf; Proposition 5, 21-move certificate appendix, numbered cards 64–127.

import Definitions.Def_Snaky21Data01
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block00_valid
open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate

theorem OAI.Snaky21.Certificate.block01_valid : Valid card_64 ∧ Valid card_65 ∧ Valid card_66 ∧ Valid card_67 ∧ Valid card_68 ∧ Valid card_69 ∧ Valid card_70 ∧ Valid card_71 ∧ Valid card_72 ∧ Valid card_73 ∧ Valid card_74 ∧ Valid card_75 ∧ Valid card_76 ∧ Valid card_77 ∧ Valid card_78 ∧ Valid card_79 ∧ Valid card_80 ∧ Valid card_81 ∧ Valid card_82 ∧ Valid card_83 ∧ Valid card_84 ∧ Valid card_85 ∧ Valid card_86 ∧ Valid card_87 ∧ Valid card_88 ∧ Valid card_89 ∧ Valid card_90 ∧ Valid card_91 ∧ Valid card_92 ∧ Valid card_93 ∧ Valid card_94 ∧ Valid card_95 ∧ Valid card_96 ∧ Valid card_97 ∧ Valid card_98 ∧ Valid card_99 ∧ Valid card_100 ∧ Valid card_101 ∧ Valid card_102 ∧ Valid card_103 ∧ Valid card_104 ∧ Valid card_105 ∧ Valid card_106 ∧ Valid card_107 ∧ Valid card_108 ∧ Valid card_109 ∧ Valid card_110 ∧ Valid card_111 ∧ Valid card_112 ∧ Valid card_113 ∧ Valid card_114 ∧ Valid card_115 ∧ Valid card_116 ∧ Valid card_117 ∧ Valid card_118 ∧ Valid card_119 ∧ Valid card_120 ∧ Valid card_121 ∧ Valid card_122 ∧ Valid card_123 ∧ Valid card_124 ∧ Valid card_125 ∧ Valid card_126 ∧ Valid card_127 ∧ True := by sorry
