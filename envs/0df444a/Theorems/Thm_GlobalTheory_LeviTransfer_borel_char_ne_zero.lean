-- Prove2me | Theorems.Thm_GlobalTheory_LeviTransfer_borel_char_ne_zero
-- name    : GlobalTheory.LeviTransfer.borel_char_ne_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:31:55.861859+00:00
-- url     : https://prove2.me/theorems/6e580648-0956-4d4d-9b0c-c5efa64c1710
-- title:
--   Levi Transfer: borel char ne zero
-- statement:
--   The Levi Transfer construction uses the borel char ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/BorelDiagNeZero.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/BorelDiagNeZero.lean#L26-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradFPfA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_BorelDiagNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.LeviTransfer
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [NumberField E] [IsCMField E]

theorem GlobalTheory.LeviTransfer.borel_char_ne_zero {Ψ : Finset (E →+* ℂ)} {r : ℕ} {b : Frame Ψ r} (hb : b ∈ Bor Ψ r)
    (la : Wt Ψ r) : bchar la b ≠ 0 := by sorry
