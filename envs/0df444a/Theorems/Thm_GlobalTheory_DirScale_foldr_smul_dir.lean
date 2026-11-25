-- Prove2me | Theorems.Thm_GlobalTheory_DirScale_foldr_smul_dir
-- name    : GlobalTheory.DirScale.foldr_smul_dir
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:52:05.553597+00:00
-- url     : https://prove2.me/theorems/de8018cb-fc26-48f4-ad3f-60e77623397f
-- title:
--   Dir Scale: foldr smul dir
-- statement:
--   The Dir Scale construction uses the foldr smul dir property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/DofIterSmulDir.lean#L41-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/DofIterSmulDir.lean#L41-L49

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

theorem GlobalTheory.DirScale.foldr_smul_dir (F : Fin d → PS R 2 d) {ι : Type} (c : ι → R) (u : ι → Fin d → R)
    (m : ι → ℕ) (f : PS R 1 d) (L : List ι) :
    L.foldr (fun l g => (Dof F (c l • u l))^[m l] g) f =
      C (L.map fun l => c l ^ m l).prod * L.foldr (fun l g => (Dof F (u l))^[m l] g) f := by sorry
