-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_FibSum_fib_card
-- name    : GlobalTheory.UnitLemma.FibSum.fib_card
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:55:47.589663+00:00
-- url     : https://prove2.me/theorems/2ec98e15-84f9-4e15-826b-23f74b450b76
-- title:
--   Fib Sum: fib card
-- statement:
--   The Fib Sum construction uses the fib card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SumStableLatticesProductEqQPowMul.lean#L15-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SumStableLatticesProductEqQPowMul.lean#L15-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardSigmaStableProdLatticeExtSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LieLatticeProdComapInlAndMapSndStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsFullLatticeProdOfComapInlMapSndStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SumStableLatticesProductEqQPowMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.FibSum

theorem GlobalTheory.UnitLemma.FibSum.fib_card (K : UQ) (B₁ B₂ : InvAlg K) (hg₁ : B₁.σ B₁.g = B₁.g) (hg₂ : B₂.σ B₂.g = B₂.g)
    (hres : resultant B₁.P B₂.P ≠ 0)
    (M₁ : Submodule K.O B₁.A) (M₂ : Submodule K.O B₂.A) (h₁ : M₁ ∈ B₁.Lin) (h₂ : M₂ ∈ B₂.Lin) :
    (Nat.card {M : Submodule K.O (B₁.A × B₂.A) // M ∈ (B₁.prod B₂).Lin ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} : ℚ) =
      (K.q : ℚ) ^ val K.O (resultant B₁.P B₂.P) := by sorry
