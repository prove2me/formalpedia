-- Prove2me | Theorems.Thm_GlobalTheory_DefectSumCompare_lrd_eq_lrdOf
-- name    : GlobalTheory.DefectSumCompare.lrd_eq_lrdOf
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:35:21.138667+00:00
-- url     : https://prove2.me/theorems/38dccf12-84b1-4466-a82c-2045f01a8942
-- title:
--   Defect Sum Compare: lrd eq lrd Of
-- statement:
--   The Defect Sum Compare construction uses the lrd eq lrd Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/BeSumStatementIffDefectSumBound.lean#L57-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/BeSumStatementIffDefectSumBound.lean#L57-L59

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_FinitePlaceArcs_BeSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SchurLatticeConjugates
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_BeSumStatementIffDefectSumBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Pointwise Formalism.L2.Pj.QAt GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
open GlobalTheory GlobalTheory.DefectSumCompare

theorem GlobalTheory.DefectSumCompare.lrd_eq_lrdOf (E : Type) [Field E] [NumberField E] : lrd E = lrdOf E := by sorry
