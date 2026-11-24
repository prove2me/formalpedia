-- Prove2me | Theorems.Thm_GlobalTheory_InertUnitOrb_class_eq_of_conj
-- name    : GlobalTheory.InertUnitOrb.class_eq_of_conj
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:15:44.706414+00:00
-- url     : https://prove2.me/theorems/70b4114d-afea-4a09-98cc-861bd7daf9a7
-- title:
--   Inert Unit Orb: class eq of conj
-- statement:
--   The Inert Unit Orb construction uses the class eq of conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNormMulOfHermitianModelUnitaryConj.lean#L24-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNormMulOfHermitianModelUnitaryConj.lean#L24-L74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfCharpolySeparableInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTraceMulOfSeparableGenerated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNormMulOfHermitianModelUnitaryConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial Matrix
noncomputable section
open GlobalTheory GlobalTheory.InertUnitOrb

theorem GlobalTheory.InertUnitOrb.class_eq_of_conj :
    ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (γ γ' u : Matrix (Fin n) (Fin n) K.E)
      (x x' : B.Aˣ) (ψ ψ' : B.A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel B γ x ψ →
      GlobalTheory.InertUnitOrb.IsModel B γ' x' ψ' → (u.map K.c)ᵀ * u = 1 → γ * u = u * γ' → B.P.Separable →
      ∃ v : B.Aˣ, (x' : B.A) = x * (v * B.σ v) := by sorry
