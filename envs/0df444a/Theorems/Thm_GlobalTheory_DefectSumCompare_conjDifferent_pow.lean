-- Prove2me | Theorems.Thm_GlobalTheory_DefectSumCompare_conjDifferent_pow
-- name    : GlobalTheory.DefectSumCompare.conjDifferent_pow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:35:30.811095+00:00
-- url     : https://prove2.me/theorems/6d3de21f-8245-4623-8baf-b04263847c07
-- title:
--   Defect Sum Compare: conj Different pow
-- statement:
--   The Defect Sum Compare construction uses the conj Different pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/BeSumStatementIffDefectSumBound.lean#L70-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/BeSumStatementIffDefectSumBound.lean#L70-L75

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

theorem GlobalTheory.DefectSumCompare.conjDifferent_pow {E K : Type} [Field E] [NumberField E] [IsGalois ℚ E] [Field K] [NumberField K]
    (σ : E →+* K) : conjDifferent σ ^ Module.finrank ℚ E = discAt E K := by sorry
