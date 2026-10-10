-- Prove2me | Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_correct
-- name    : OAI.SnakyCertificate.MilestoneChecks.block04_correct
-- status  : Open
-- author  : @Yuxuan Xu
-- created : 2026-10-09T14:24:04.18932+00:00
-- url     : https://prove2.me/theorems/538fc2c8-b861-41ac-85f1-1339384a4046
-- title:
--   35-move certificate: exact rows 128–159
-- statement:
--   Original certificate rows 128 through 159 equal the explicit candidate required set, envelope and height; each row has the required subset/origin/height invariants. The nonbase entries have their exact indices, nonempty placement lists and strictly backward references.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SnakyCertificate.lean

import Definitions.Def_Snaky35Cache04
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate

theorem OAI.SnakyCertificate.MilestoneChecks.block04_correct : (rowAt 128 = data_128 ∧ Good (rowAt 128) ∧ EntryGood 128) ∧ (rowAt 129 = data_129 ∧ Good (rowAt 129) ∧ EntryGood 129) ∧ (rowAt 130 = data_130 ∧ Good (rowAt 130) ∧ EntryGood 130) ∧ (rowAt 131 = data_131 ∧ Good (rowAt 131) ∧ EntryGood 131) ∧ (rowAt 132 = data_132 ∧ Good (rowAt 132) ∧ EntryGood 132) ∧ (rowAt 133 = data_133 ∧ Good (rowAt 133) ∧ EntryGood 133) ∧ (rowAt 134 = data_134 ∧ Good (rowAt 134) ∧ EntryGood 134) ∧ (rowAt 135 = data_135 ∧ Good (rowAt 135) ∧ EntryGood 135) ∧ (rowAt 136 = data_136 ∧ Good (rowAt 136) ∧ EntryGood 136) ∧ (rowAt 137 = data_137 ∧ Good (rowAt 137) ∧ EntryGood 137) ∧ (rowAt 138 = data_138 ∧ Good (rowAt 138) ∧ EntryGood 138) ∧ (rowAt 139 = data_139 ∧ Good (rowAt 139) ∧ EntryGood 139) ∧ (rowAt 140 = data_140 ∧ Good (rowAt 140) ∧ EntryGood 140) ∧ (rowAt 141 = data_141 ∧ Good (rowAt 141) ∧ EntryGood 141) ∧ (rowAt 142 = data_142 ∧ Good (rowAt 142) ∧ EntryGood 142) ∧ (rowAt 143 = data_143 ∧ Good (rowAt 143) ∧ EntryGood 143) ∧ (rowAt 144 = data_144 ∧ Good (rowAt 144) ∧ EntryGood 144) ∧ (rowAt 145 = data_145 ∧ Good (rowAt 145) ∧ EntryGood 145) ∧ (rowAt 146 = data_146 ∧ Good (rowAt 146) ∧ EntryGood 146) ∧ (rowAt 147 = data_147 ∧ Good (rowAt 147) ∧ EntryGood 147) ∧ (rowAt 148 = data_148 ∧ Good (rowAt 148) ∧ EntryGood 148) ∧ (rowAt 149 = data_149 ∧ Good (rowAt 149) ∧ EntryGood 149) ∧ (rowAt 150 = data_150 ∧ Good (rowAt 150) ∧ EntryGood 150) ∧ (rowAt 151 = data_151 ∧ Good (rowAt 151) ∧ EntryGood 151) ∧ (rowAt 152 = data_152 ∧ Good (rowAt 152) ∧ EntryGood 152) ∧ (rowAt 153 = data_153 ∧ Good (rowAt 153) ∧ EntryGood 153) ∧ (rowAt 154 = data_154 ∧ Good (rowAt 154) ∧ EntryGood 154) ∧ (rowAt 155 = data_155 ∧ Good (rowAt 155) ∧ EntryGood 155) ∧ (rowAt 156 = data_156 ∧ Good (rowAt 156) ∧ EntryGood 156) ∧ (rowAt 157 = data_157 ∧ Good (rowAt 157) ∧ EntryGood 157) ∧ (rowAt 158 = data_158 ∧ Good (rowAt 158) ∧ EntryGood 158) ∧ (rowAt 159 = data_159 ∧ Good (rowAt 159) ∧ EntryGood 159) ∧ True := by sorry
