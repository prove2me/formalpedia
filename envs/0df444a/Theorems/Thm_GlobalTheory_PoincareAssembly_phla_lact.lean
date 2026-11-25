-- Prove2me | Theorems.Thm_GlobalTheory_PoincareAssembly_phla_lact
-- name    : GlobalTheory.PoincareAssembly.phla_lact
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:49:41.993563+00:00
-- url     : https://prove2.me/theorems/5820d25b-3f41-5808-a3f9-1be992139391
-- title:
--   Poincare Assembly: phla lact
-- statement:
--   The Poincare Assembly construction uses the phla lact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/PoinStatementOf.lean#L44-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/PoinStatementOf.lean#L44-L47

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PoinStatementOf
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
open GlobalTheory GlobalTheory.PoincareAssembly
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.PoincareAssembly.phla_lact {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    (x : Frame X.Ψ r) : phla X la (lact γ x) = phla X la x := by sorry
