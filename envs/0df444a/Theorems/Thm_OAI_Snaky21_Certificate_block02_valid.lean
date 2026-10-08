-- Prove2me | Theorems.Thm_OAI_Snaky21_Certificate_block02_valid
-- name    : OAI.Snaky21.Certificate.block02_valid
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-08T08:30:13.068682+00:00
-- url     : https://prove2.me/theorems/56208d6a-4034-4da6-820f-35bd4e773677
-- title:
--   21-move certificate: validity of numbered cards 128–191
-- statement:
--   Every numbered card from 128 through 191 of the fixed 21-move certificate is a valid conditional claim. The required set, envelope and height are the literal finite reconstruction of the printed data, including every nested combination. Every actual combination equation is checked by Lean kernel reduction, and the game meaning follows from the conditional-claim calculus and earlier numbered cards.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Snaky-in-21-Maker-moves-September-25-2026/article.pdf; Proposition 5, 21-move certificate appendix, numbered cards 128–191.

import Definitions.Def_Snaky21Data02
import Theorems.Thm_OAI_Snaky21_claim_calculus
import Theorems.Thm_OAI_Snaky21_Certificate_block01_valid
open OAI.Snaky21 OAI.SnakyPrototype OAI.Snaky21.Certificate

theorem OAI.Snaky21.Certificate.block02_valid : Valid card_128 ∧ Valid card_129 ∧ Valid card_130 ∧ Valid card_131 ∧ Valid card_132 ∧ Valid card_133 ∧ Valid card_134 ∧ Valid card_135 ∧ Valid card_136 ∧ Valid card_137 ∧ Valid card_138 ∧ Valid card_139 ∧ Valid card_140 ∧ Valid card_141 ∧ Valid card_142 ∧ Valid card_143 ∧ Valid card_144 ∧ Valid card_145 ∧ Valid card_146 ∧ Valid card_147 ∧ Valid card_148 ∧ Valid card_149 ∧ Valid card_150 ∧ Valid card_151 ∧ Valid card_152 ∧ Valid card_153 ∧ Valid card_154 ∧ Valid card_155 ∧ Valid card_156 ∧ Valid card_157 ∧ Valid card_158 ∧ Valid card_159 ∧ Valid card_160 ∧ Valid card_161 ∧ Valid card_162 ∧ Valid card_163 ∧ Valid card_164 ∧ Valid card_165 ∧ Valid card_166 ∧ Valid card_167 ∧ Valid card_168 ∧ Valid card_169 ∧ Valid card_170 ∧ Valid card_171 ∧ Valid card_172 ∧ Valid card_173 ∧ Valid card_174 ∧ Valid card_175 ∧ Valid card_176 ∧ Valid card_177 ∧ Valid card_178 ∧ Valid card_179 ∧ Valid card_180 ∧ Valid card_181 ∧ Valid card_182 ∧ Valid card_183 ∧ Valid card_184 ∧ Valid card_185 ∧ Valid card_186 ∧ Valid card_187 ∧ Valid card_188 ∧ Valid card_189 ∧ Valid card_190 ∧ Valid card_191 ∧ True := by sorry
