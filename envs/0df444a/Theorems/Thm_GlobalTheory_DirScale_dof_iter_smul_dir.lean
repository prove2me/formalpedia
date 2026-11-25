-- Prove2me | Theorems.Thm_GlobalTheory_DirScale_dof_iter_smul_dir
-- name    : GlobalTheory.DirScale.dof_iter_smul_dir
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:52:09.421247+00:00
-- url     : https://prove2.me/theorems/4f710749-6760-4880-b3c9-a41b46b2da15
-- title:
--   Dir Scale: dof iter smul dir
-- statement:
--   The Dir Scale construction uses the dof iter smul dir property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/DofIterSmulDir.lean#L33-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/DofIterSmulDir.lean#L33-L39

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

theorem GlobalTheory.DirScale.dof_iter_smul_dir (F : Fin d → PS R 2 d) (c : R) (u : Fin d → R) (n : ℕ) (f : PS R 1 d) :
    (Dof F (c • u))^[n] f = C (c ^ n) * (Dof F u)^[n] f := by sorry
