-- Prove2me | Theorems.Thm_GlobalTheory_AnLogRes_isIrreducibleAnalytic_univ
-- name    : GlobalTheory.AnLogRes.isIrreducibleAnalytic_univ
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:30:25.662887+00:00
-- url     : https://prove2.me/theorems/561773fa-de8d-4fe5-a663-78cab9c8144d
-- title:
--   An Log Res: is Irreducible Analytic univ
-- statement:
--   The An Log Res construction uses the is Irreducible Analytic univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/LogResolutionProjectiveLine.lean#L70-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/LogResolutionProjectiveLine.lean#L70-L79

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PushAFinsumInter
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AnalyticLogResolution
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__LogResolutionProjectiveLine_09840aae280abe50
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt
open GlobalTheory.AnLogRes
variable {d : ℕ} {X : Type} [TopologicalSpace X]

theorem GlobalTheory.AnLogRes.isIrreducibleAnalytic_univ [ConnectedSpace X] (A : FinHolAtlas d X) :
    IsIrreducibleAnalytic A Set.univ := by sorry
