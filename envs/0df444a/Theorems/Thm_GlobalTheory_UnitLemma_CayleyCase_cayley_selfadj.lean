-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_CayleyCase_cayley_selfadj
-- name    : GlobalTheory.UnitLemma.CayleyCase.cayley_selfadj
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:56:23.414087+00:00
-- url     : https://prove2.me/theorems/cbebea7a-fd7e-4a33-816d-1d081d374ba3
-- title:
--   Cayley Case: cayley selfadj
-- statement:
--   The Cayley Case construction uses the cayley selfadj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaResiduallyUnipotentViaCayley.lean#L170-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnitLemmaResiduallyUnipotentViaCayley.lean#L170-L191

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyMulLeftSeparableOfAdjoinEqTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.CayleyCase
variable {K : UQ}

theorem GlobalTheory.UnitLemma.CayleyCase.cayley_selfadj (B : InvAlg K) (s ε : K.O) (Y : B.A) (hu : B.g * B.σ B.g = 1)
    (hs : algebraMap K.O K.E s * K.c (algebraMap K.O K.E s) = 1)
    (hε : K.c (algebraMap K.O K.E ε) = -algebraMap K.O K.E ε)
    (w : B.A) (hw : (B.g + algebraMap K.O B.A s) * w = 1)
    (hY : Y * (B.g + algebraMap K.O B.A s) = algebraMap K.O B.A ε * (B.g - algebraMap K.O B.A s)) :
    B.σ Y = Y := by sorry
