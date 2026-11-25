-- Prove2me | Theorems.Thm_GlobalTheory_AnLogRes_eq_univ_of_interior_nonempty
-- name    : GlobalTheory.AnLogRes.eq_univ_of_interior_nonempty
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:30:27.173468+00:00
-- url     : https://prove2.me/theorems/7155bece-9ee4-4898-8873-c49b6edbaff8
-- title:
--   An Log Res: eq univ of interior nonempty
-- statement:
--   The An Log Res construction uses the eq univ of interior nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/LogResolutionProjectiveLine.lean#L34-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/LogResolutionProjectiveLine.lean#L34-L68

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

theorem GlobalTheory.AnLogRes.eq_univ_of_interior_nonempty [PreconnectedSpace X] (A : FinHolAtlas d X) {S : Set X}
    (hS : A.IsAnalyticSubset S) (h : (interior S).Nonempty) : S = Set.univ := by sorry
