-- Prove2me | Theorems.Thm_GlobalTheory_MinorFrame_RatProj_fockS_map
-- name    : GlobalTheory.MinorFrame.RatProj.fockS_map
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:06:22.29984+00:00
-- url     : https://prove2.me/theorems/003c9bae-58f4-4300-86f4-b15d51e3dd9c
-- title:
--   Rat Proj: fock S map
-- statement:
--   The Rat Proj construction uses the fock S map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsRationalFockProjectionMaximalMinors.lean#L50-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsRationalFockProjectionMaximalMinors.lean#L50-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsRationalFockProjectionMaximalMinors
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MeasureTheory
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.MinorFrame GlobalTheory.MinorFrame.RatProj
variable {σ : Type}

theorem GlobalTheory.MinorFrame.RatProj.fockS_map (f g : MvPolynomial σ ℚ) :
    Formalism.L2.DIV.fockS (map (algebraMap ℚ ℂ) f) (map (algebraMap ℚ ℂ) g) = (fockQ f g : ℂ) := by sorry
