-- Prove2me | Theorems.Thm_GlobalTheory_HodgeCurvPoint_form_map_self
-- name    : GlobalTheory.HodgeCurvPoint.form_map_self
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:49:36.626974+00:00
-- url     : https://prove2.me/theorems/0397581b-b3cc-4d5d-93fe-027dbb3b6103
-- title:
--   Hodge Curv Point: form map self
-- statement:
--   The Hodge Curv Point construction uses the form map self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeCurvatureDualMetricPointwiseBound.lean#L24-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HodgeCurvatureDualMetricPointwiseBound.lean#L24-L30

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

theorem GlobalTheory.HodgeCurvPoint.form_map_self {M : Matrix (Fin g) (Fin g) ℝ} (hM : M.IsSymm) (v : Fin g → ℂ) :
    form (M.map ofReal) v v = (((fun j => (v j).re) ⬝ᵥ M *ᵥ (fun j => (v j).re) +
      (fun j => (v j).im) ⬝ᵥ M *ᵥ (fun j => (v j).im) : ℝ) : ℂ) := by sorry
