-- Prove2me | Theorems.Thm_GlobalTheory_CharacterColumns_dmonOf_congr_dir
-- name    : GlobalTheory.CharacterColumns.dmonOf_congr_dir
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:57:39.358586+00:00
-- url     : https://prove2.me/theorems/ff2a4ac1-4e78-4ac6-841b-b7691021f422
-- title:
--   Character Columns: dmon Of congr dir
-- statement:
--   The Character Columns construction uses the dmon Of congr dir property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ConstantCoeffDmonOfEigen.lean#L18-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ConstantCoeffDmonOfEigen.lean#L18-L26

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

theorem GlobalTheory.CharacterColumns.dmonOf_congr_dir {R : Type} [CommRing R] {d : ℕ} (F : Fin d → PS R 2 d) {ι : Type}
    [Fintype ι] (u u' : ι → Fin d → R) (mo : ι →₀ ℕ) (hu : ∀ l, mo l ≠ 0 → u l = u' l)
    (f : PS R 1 d) : DmonOf F u mo f = DmonOf F u' mo f := by sorry
