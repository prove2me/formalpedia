-- Prove2me | Theorems.Thm_GlobalTheory_CharacterColumns_dof_zero_dir
-- name    : GlobalTheory.CharacterColumns.dof_zero_dir
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:57:47.482161+00:00
-- url     : https://prove2.me/theorems/e04cdc58-be23-45a8-868e-e261accca53e
-- title:
--   Character Columns: dof zero dir
-- statement:
--   The Character Columns construction uses the dof zero dir property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ConstantCoeffDmonOfEigen.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ConstantCoeffDmonOfEigen.lean#L14-L16

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfSubMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NabValColumnsCongr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ConstantCoeffDmonOfEigen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.CharacterColumns

theorem GlobalTheory.CharacterColumns.dof_zero_dir {R : Type} [CommRing R] {d : ℕ} (F : Fin d → PS R 2 d) (f : PS R 1 d) :
    Dof F 0 f = 0 := by sorry
