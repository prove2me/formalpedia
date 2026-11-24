-- Prove2me | Theorems.Thm_GlobalTheory_JHypEquiv_secondCountable_K
-- name    : GlobalTheory.JHypEquiv.secondCountable_K
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:23:41.907246+00:00
-- url     : https://prove2.me/theorems/29b1a34a-eb7b-4602-97ff-c8b6d2b72af9
-- title:
--   JHyp Equiv: second Countable K
-- statement:
--   The JHyp Equiv construction uses the second Countable K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JHypUnipotentTorusEquivariance.lean#L12-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JHypUnipotentTorusEquivariance.lean#L12-L18

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

theorem GlobalTheory.JHypEquiv.secondCountable_K [Unram F E] (A : Et F E) : SecondCountableTopology A.K := by sorry
