-- Prove2me | Theorems.Thm_GlobalTheory_CharacterColumns_constantCoeff_dmonOf_eigen
-- name    : GlobalTheory.CharacterColumns.constantCoeff_dmonOf_eigen
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:57:31.731805+00:00
-- url     : https://prove2.me/theorems/0f14e0a1-71bc-4458-b59a-3f4392f71c05
-- title:
--   Character Columns: constant Coeff dmon Of eigen
-- statement:
--   The Character Columns construction uses the constant Coeff dmon Of eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ConstantCoeffDmonOfEigen.lean#L38-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ConstantCoeffDmonOfEigen.lean#L38-L56

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

theorem GlobalTheory.CharacterColumns.constantCoeff_dmonOf_eigen {R : Type} [CommRing R] {d : ℕ} (F : Fin d → PS R 2 d) {ι : Type}
    [Fintype ι] (u : ι → Fin d → R) (S : Set ι) (χ : PS R 1 d) (y : ι → R)
    (h1 : constantCoeff χ = 1) (hχ : ∀ l ∈ S, Dof F (u l) χ = C (y l) * χ) (mo : ι →₀ ℕ)
    (hmo : ∀ l, mo l ≠ 0 → l ∈ S) :
    constantCoeff (DmonOf F (S.indicator u) mo χ) = ∏ l, y l ^ mo l := by sorry
