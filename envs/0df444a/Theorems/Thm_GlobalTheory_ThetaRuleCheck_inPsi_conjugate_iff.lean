-- Prove2me | Theorems.Thm_GlobalTheory_ThetaRuleCheck_inPsi_conjugate_iff
-- name    : GlobalTheory.ThetaRuleCheck.inPsi_conjugate_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:24.463578+00:00
-- url     : https://prove2.me/theorems/cedad948-b1f4-4ee1-8dfd-2425f769e614
-- title:
--   Theta Rule Check: in Psi conjugate iff
-- statement:
--   The Theta Rule Check construction uses the in Psi conjugate iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/TotalDegreeEqOfMemHarmA.lean#L11-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/TotalDegreeEqOfMemHarmA.lean#L11-L42

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_TotalDegreeEqOfMemHarmA
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
open GlobalTheory GlobalTheory.ThetaRuleCheck
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField MvPolynomial
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem GlobalTheory.ThetaRuleCheck.inPsi_conjugate_iff (τ : E →+* ℂ) : InPsi H (ComplexEmbedding.conjugate τ) ↔ ¬ InPsi H τ := by sorry
