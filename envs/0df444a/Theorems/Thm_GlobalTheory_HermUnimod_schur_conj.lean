-- Prove2me | Theorems.Thm_GlobalTheory_HermUnimod_schur_conj
-- name    : GlobalTheory.HermUnimod.schur_conj
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:20:11.834303+00:00
-- url     : https://prove2.me/theorems/afa8210a-bd8b-409f-9b2f-fb5cba8485b3
-- title:
--   Herm Unimod: schur conj
-- statement:
--   The Herm Unimod construction uses the schur conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnimodularHermitianMatrixCongruentOne.lean#L83-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnimodularHermitianMatrixCongruentOne.lean#L83-L86

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormOneAddEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHermitianMatrixCongruentOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.HermUnimod
variable {E : Type} [NormedField E] [IsUltrametricDist E] [StarRing E]

theorem GlobalTheory.HermUnimod.schur_conj {m : Type} [Fintype m] [DecidableEq m] (A : Matrix m m E) (B : Matrix m Unit E) :
    (fromBlocks 1 0 (-Bᴴ) 1 : Matrix (m ⊕ Unit) (m ⊕ Unit) E)ᴴ * fromBlocks A B Bᴴ 1 *
        fromBlocks 1 0 (-Bᴴ) 1 = fromBlocks (A - B * Bᴴ) 0 0 1 := by sorry
