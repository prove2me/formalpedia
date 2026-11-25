-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_CayleyAny_mobius_selfadj
-- name    : GlobalTheory.UnitLemma.CayleyAny.mobius_selfadj
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:03:24.684567+00:00
-- url     : https://prove2.me/theorems/69ef743c-da00-47f6-9937-7a42e3e2849e
-- title:
--   Cayley Any: mobius selfadj
-- statement:
--   The Cayley Any construction uses the mobius selfadj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitLemmaResiduallyUnipotentCayleyTransform.lean#L74-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitLemmaResiduallyUnipotentCayleyTransform.lean#L74-L99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitLemmaResiduallyUnipotentViaCayley
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitLemmaResiduallyUnipotentCayleyTransform
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
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.CayleyAny
open GlobalTheory.UnitLemma.CayleyCase
variable {K : UQ}

theorem GlobalTheory.UnitLemma.CayleyAny.mobius_selfadj (B : InvAlg K) (x y ξ : K.O) (Y : B.A) (hu : B.g * B.σ B.g = 1)
    (hxy : K.c (algebraMap K.O K.E x) = algebraMap K.O K.E y)
    (hξ : algebraMap K.O K.E ξ * K.c (algebraMap K.O K.E ξ) = 1)
    (w : B.A) (hw : (B.g - algebraMap K.O B.A ξ) * w = 1)
    (hY : Y * (B.g - algebraMap K.O B.A ξ) =
      algebraMap K.O B.A y * B.g - algebraMap K.O B.A x * algebraMap K.O B.A ξ) :
    B.σ Y = Y := by sorry
