-- Prove2me | Theorems.Thm_GlobalTheory_DirScale_dof_iter_C_mul
-- name    : GlobalTheory.DirScale.dof_iter_C_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:49:57.17588+00:00
-- url     : https://prove2.me/theorems/243b2e2c-ff6b-4f26-a172-5e760646ed76
-- title:
--   Dir Scale: dof iter C mul
-- statement:
--   The Dir Scale construction uses the dof iter C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/DofIterSmulDir.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/DofIterSmulDir.lean#L26-L31

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

theorem GlobalTheory.DirScale.dof_iter_C_mul (F : Fin d → PS R 2 d) (u : Fin d → R) (n : ℕ) (r : R) (f : PS R 1 d) :
    (Dof F u)^[n] (C r * f) = C r * (Dof F u)^[n] f := by sorry
