-- Prove2me | Theorems.Thm_GlobalTheory_JHypEquiv_row_one
-- name    : GlobalTheory.JHypEquiv.row_one
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:23:44.119085+00:00
-- url     : https://prove2.me/theorems/ae8ce1e5-64db-4a23-9ea8-45e70508d55b
-- title:
--   JHyp Equiv: row one
-- statement:
--   The JHyp Equiv construction uses the row one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JHypUnipotentTorusEquivariance.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JHypUnipotentTorusEquivariance.lean#L26-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnifConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JHypUnipotentTorusEquivariance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JHypEquiv
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem GlobalTheory.JHypEquiv.row_one (A : Et F E) (z : A.K) (s : A.Kˣ) (g : SpecialLinearGroup (Fin 2) A.K) (j : Fin 2) :
    (nS z * mS s * g) 1 j = ((s⁻¹ : A.Kˣ) : A.K) * g 1 j := by sorry
