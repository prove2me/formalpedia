-- Prove2me | Theorems.Thm_GlobalTheory_MajNear_gram_isom
-- name    : GlobalTheory.MajNear.gram_isom
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:33:57.272611+00:00
-- url     : https://prove2.me/theorems/d5cb1ba0-d0dc-4029-88a9-f27e9667d516
-- title:
--   Maj Near: gram isom
-- statement:
--   The Maj Near construction uses the gram isom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/IsomOfGramEq.lean#L49-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/IsomOfGramEq.lean#L49-L53

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IsomOfGramEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexConjugate
open GlobalTheory GlobalTheory.MajNear
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [NumberField E] [IsCMField E]

theorem GlobalTheory.MajNear.gram_isom {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    {g : Matrix (Fin r) (Fin r) ℂ} (hg : ∀ u v, hermC τ G (g *ᵥ u) (g *ᵥ v) = hermC τ G u v)
    (M : Matrix (Fin r) (Fin r) ℂ) : gram τ G (g * M) = gram τ G M := by sorry
