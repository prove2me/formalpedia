-- Prove2me | Theorems.Thm_GlobalTheory_BK_isHausdorff_S
-- name    : GlobalTheory.BK.isHausdorff_S
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:00:27.240812+00:00
-- url     : https://prove2.me/theorems/db7cf645-8592-490c-980a-60103d02f898
-- title:
--   BK: is Hausdorff S
-- statement:
--   The BK construction uses the is Hausdorff S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemSpanLPowSIff.lean#L45-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MemSpanLPowSIff.lean#L45-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MemSpanLPowSIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BK PowerSeries Filter Topology
open GlobalTheory GlobalTheory.BK
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]

theorem GlobalTheory.BK.isHausdorff_S : IsHausdorff (Ideal.span {(l : S O K e)}) (S O K e) := by sorry
