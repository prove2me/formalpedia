-- Prove2me | Theorems.Thm_GlobalTheory_DefectSumCompare_vla_discAt
-- name    : GlobalTheory.DefectSumCompare.vla_discAt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:23.030945+00:00
-- url     : https://prove2.me/theorems/210775a7-ae96-433f-b214-36ee4fba35b0
-- title:
--   Defect Sum Compare: vla disc At
-- statement:
--   The Defect Sum Compare construction uses the vla disc At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/BeSumStatementIffDefectSumBound.lean#L86-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/BeSumStatementIffDefectSumBound.lean#L86-L88

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

theorem GlobalTheory.DefectSumCompare.vla_discAt (σ : E →+* K) (la : HeightOneSpectrum (𝓞 K)) :
    vla la (discAt E K) = Module.finrank ℚ E * ord_vw la (conjDifferent σ) := by sorry
