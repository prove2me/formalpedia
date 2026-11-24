-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_Bmp_mem_lam
-- name    : GlobalTheory.ThK.Dbl.Bmp.mem_lam
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:05.906159+00:00
-- url     : https://prove2.me/theorems/2b68ee3b-f24c-4888-864c-d1fed1228e38
-- title:
--   Bmp: mem lam
-- statement:
--   The Bmp construction uses the mem lam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/MemLam.lean#L64-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/MemLam.lean#L64-L65

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_MemLam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Bmp
open Matrix
variable {O K : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K]
variable {a : O} {n d : ℕ}
omit [IsDomain O] [IsPrincipalIdealRing O] [IsFractionRing O K]

theorem GlobalTheory.ThK.Dbl.Bmp.mem_lam {Y : Matrix (Fin n) (Fin d) K} : Y ∈ lam K a n d ↔ ∃ α : Matrix (Fin n) (Fin d) O, a • α.map (algebraMap O K) = Y := by sorry
