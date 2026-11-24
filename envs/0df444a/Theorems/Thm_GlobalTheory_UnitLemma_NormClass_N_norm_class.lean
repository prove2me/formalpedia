-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_NormClass_N_norm_class
-- name    : GlobalTheory.UnitLemma.NormClass.N_norm_class
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:27:20.003469+00:00
-- url     : https://prove2.me/theorems/628844b9-e53a-4998-8a2f-be2f0ae2d3ef
-- title:
--   Norm Class: N norm class
-- statement:
--   The Norm Class construction uses the N norm class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LatticeCountAndGramDetSignNormClass.lean#L107-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LatticeCountAndGramDetSignNormClass.lean#L107-L176

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeCountAndGramDetSignNormClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.NormClass
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial
variable {K : UQ}
open Polynomial
variable {K : _root_.GlobalTheory.UnitLemma.UQ}

theorem GlobalTheory.UnitLemma.NormClass.N_norm_class : ∀ (K : _root_.GlobalTheory.UnitLemma.UQ) (B : _root_.GlobalTheory.UnitLemma.InvAlg K) (x : B.A) (u : B.Aˣ),
    B.N (x * (u * B.σ (u : B.A))) = B.N x ∧
      K.eta (B.gramDet (x * (u * B.σ (u : B.A)))) = K.eta (B.gramDet x) := by sorry
