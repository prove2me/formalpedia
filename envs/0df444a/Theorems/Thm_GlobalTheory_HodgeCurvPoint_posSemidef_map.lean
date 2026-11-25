-- Prove2me | Theorems.Thm_GlobalTheory_HodgeCurvPoint_posSemidef_map
-- name    : GlobalTheory.HodgeCurvPoint.posSemidef_map
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:49:24.866793+00:00
-- url     : https://prove2.me/theorems/a2905bbb-158c-4b68-b375-ff4f249b6f0d
-- title:
--   Hodge Curv Point: pos Semidef map
-- statement:
--   The Hodge Curv Point construction uses the pos Semidef map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeCurvatureDualMetricPointwiseBound.lean#L32-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeCurvatureDualMetricPointwiseBound.lean#L32-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeCurvatureDualMetricPointwiseBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.HodgeCurvPoint
variable {g : ℕ}

theorem GlobalTheory.HodgeCurvPoint.posSemidef_map {M : Matrix (Fin g) (Fin g) ℝ} (hM : M.IsSymm)
    (h : ∀ x, 0 ≤ x ⬝ᵥ M *ᵥ x) : (M.map ofReal).PosSemidef := by sorry
