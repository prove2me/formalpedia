-- Prove2me | Theorems.Thm_GlobalTheory_DefectSumCompare_finrank_mul_defect
-- name    : GlobalTheory.DefectSumCompare.finrank_mul_defect
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:35:52.253818+00:00
-- url     : https://prove2.me/theorems/10605beb-7e6a-4f07-bc45-0f34cd9d5a9d
-- title:
--   Defect Sum Compare: finrank mul defect
-- statement:
--   The Defect Sum Compare construction uses the finrank mul defect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/BeSumStatementIffDefectSumBound.lean#L110-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/BeSumStatementIffDefectSumBound.lean#L110-L115

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
variable {E K : Type} [Field E] [NumberField E] [IsGalois ℚ E] [Field K] [NumberField K]

theorem GlobalTheory.DefectSumCompare.finrank_mul_defect (hσ : Nonempty (E →+* K)) (n' : ℕ+) (a : ℕ)
    (la : HeightOneSpectrum (𝓞 K)) :
    (Module.finrank ℚ E : ℝ) * defect_vw E n' a la =
      beOf E ((n' : ℕ) ^ Module.finrank ℚ E) a la := by sorry
