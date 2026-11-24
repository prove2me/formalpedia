-- Prove2me | Theorems.Thm_GlobalTheory_InertUnitOrb_conj_of_norm_class
-- name    : GlobalTheory.InertUnitOrb.conj_of_norm_class
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:15:26.230926+00:00
-- url     : https://prove2.me/theorems/0cb1012b-aee8-4a2a-b3c8-13b269bcc6b0
-- title:
--   Inert Unit Orb: conj of norm class
-- statement:
--   The Inert Unit Orb construction uses the conj of norm class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HermitianModelsConjUnitaryOfNormClass.lean#L8-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HermitianModelsConjUnitaryOfNormClass.lean#L8-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianModelsConjUnitaryOfNormClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial Matrix
open GlobalTheory GlobalTheory.InertUnitOrb

theorem GlobalTheory.InertUnitOrb.conj_of_norm_class (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ)
    (γ γ' : Matrix (Fin n) (Fin n) K.E) (x x' v : B.Aˣ) (ψ ψ' : B.A ≃ₗ[K.E] (Fin n → K.E))
    (h : GlobalTheory.InertUnitOrb.IsModel B γ x ψ) (h' : GlobalTheory.InertUnitOrb.IsModel B γ' x' ψ')
    (hx : (x' : B.A) = x * (v * B.σ v)) :
    ∃ u : Matrix (Fin n) (Fin n) K.E, (u.map K.c)ᵀ * u = 1 ∧ γ * u = u * γ' := by sorry
