-- Prove2me | Theorems.Thm_GlobalTheory_DirScale_dmonOf_smul_dir
-- name    : GlobalTheory.DirScale.dmonOf_smul_dir
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:55:50.513805+00:00
-- url     : https://prove2.me/theorems/a70342dc-fd33-4726-bdaa-0fa0e56450e7
-- title:
--   Dir Scale: dmon Of smul dir
-- statement:
--   The Dir Scale construction uses the dmon Of smul dir property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/DofIterSmulDir.lean#L51-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/DofIterSmulDir.lean#L51-L59

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_DofIterSmulDir
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
open GlobalTheory GlobalTheory.DirScale
variable {R : Type} [CommRing R] {d : ℕ}

theorem GlobalTheory.DirScale.dmonOf_smul_dir : ∀ (R : Type) [CommRing R] (d : ℕ) (F : Fin d → PS R 2 d) (ι : Type)
    [Fintype ι] (c : ι → R) (u : ι → Fin d → R) (m : ι →₀ ℕ) (f : PS R 1 d),
    DmonOf F (fun l => c l • u l) m f = C (∏ l, c l ^ m l) * DmonOf F u m f := by sorry
