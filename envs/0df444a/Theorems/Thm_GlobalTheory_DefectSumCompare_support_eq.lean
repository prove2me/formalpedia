-- Prove2me | Theorems.Thm_GlobalTheory_DefectSumCompare_support_eq
-- name    : GlobalTheory.DefectSumCompare.support_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:03:56.529846+00:00
-- url     : https://prove2.me/theorems/9a8fca84-ce7b-539e-8a2f-f67d4598781b
-- title:
--   Defect Sum Compare: support eq
-- statement:
--   The Defect Sum Compare construction uses the support eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/BeSumStatementIffDefectSumBound.lean#L117-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/BeSumStatementIffDefectSumBound.lean#L117-L123

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

theorem GlobalTheory.DefectSumCompare.support_eq (hσ : Nonempty (E →+* K)) (n' : ℕ+) (a : ℕ) :
    Function.support (defect_vw E (K := K) n' a) =
      Function.support (beOf E (K := K) ((n' : ℕ) ^ Module.finrank ℚ E) a) := by sorry
