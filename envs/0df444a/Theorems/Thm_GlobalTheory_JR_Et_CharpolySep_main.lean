-- Prove2me | Theorems.Thm_GlobalTheory_JR_Et_CharpolySep_main
-- name    : GlobalTheory.JR.Et.CharpolySep.main
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:11:21.415478+00:00
-- url     : https://prove2.me/theorems/36803633-b666-532d-9cfd-9bfd09beaa37
-- title:
--   Charpoly Sep: main
-- statement:
--   The Charpoly Sep construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyEtaleGeneratorMulMatrixSeparable.lean#L53-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyEtaleGeneratorMulMatrixSeparable.lean#L53-L83

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulMatMemUnitaryGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyEtaleGeneratorMulMatrixSeparable
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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Et GlobalTheory.JR.Et.CharpolySep

theorem GlobalTheory.JR.Et.CharpolySep.main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F), A.IsGen τ p →
    ∀ (j : A.L ≃ₗ[E] (Fin r → E)) (B : Matrix (Fin r) (Fin r) E),
      (∀ z, j (algebraMap A.K A.L τ * z) = B *ᵥ j z) → B.charpoly.Separable := by sorry
