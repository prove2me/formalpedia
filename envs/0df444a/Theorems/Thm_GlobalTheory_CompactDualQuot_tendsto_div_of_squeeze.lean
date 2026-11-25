-- Prove2me | Theorems.Thm_GlobalTheory_CompactDualQuot_tendsto_div_of_squeeze
-- name    : GlobalTheory.CompactDualQuot.tendsto_div_of_squeeze
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:07:53.371953+00:00
-- url     : https://prove2.me/theorems/ae2af0b2-cb62-55f9-ae7a-efdd4f7b7994
-- title:
--   Compact Dual Quot: tendsto div of squeeze
-- statement:
--   The Compact Dual Quot construction uses the tendsto div of squeeze property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ContinuousMatrixEntryAbsSum.lean#L97-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ContinuousMatrixEntryAbsSum.lean#L97-L139

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_PerpendicularEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ContinuousMatrixEntryAbsSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompactDualQuot
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
open scoped ENNReal
variable {P Q P' Q' : ℕ}

theorem GlobalTheory.CompactDualQuot.tendsto_div_of_squeeze {F V A : ℝ → ℝ≥0∞} {n : ℕ} {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hV : ∀ t r : ℝ, 0 < t → 0 < r → V (t * r) = ENNReal.ofReal (t ^ n) * V r)
    (hF : Tendsto (fun r => F r / V r) (𝓝[>] 0) (𝓝 c))
    (hA : ∀ t : ℝ, 1 < t → ∀ᶠ r in 𝓝[>] (0 : ℝ), F (t⁻¹ * r) ≤ A r ∧ A r ≤ F (t * r)) :
    Tendsto (fun r => A r / V r) (𝓝[>] 0) (𝓝 c) := by sorry
