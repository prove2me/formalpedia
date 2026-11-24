-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_LD_toGL_val
-- name    : GlobalTheory.ThK.Dbl.LD.toGL_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:55.761299+00:00
-- url     : https://prove2.me/theorems/b60dc20c-f6e3-47ff-811a-5d3aa6d9ea3b
-- title:
--   LD: to GL val
-- statement:
--   The LD construction uses the to GL val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistE.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistE.lean#L23-L24

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistB
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistD
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology GlobalTheory.WeilM Matrix
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.LD
variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [ContinuousInv₀ k] [T2Space k] {d : ℕ}

theorem GlobalTheory.ThK.Dbl.LD.toGL_val {X : Matrix (Fin d) (Fin d) k} (h : X.det ≠ 0) : (toGL X).1 = X := by sorry
