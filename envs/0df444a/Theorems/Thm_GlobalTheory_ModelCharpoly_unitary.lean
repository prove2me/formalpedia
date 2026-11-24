-- Prove2me | Theorems.Thm_GlobalTheory_ModelCharpoly_unitary
-- name    : GlobalTheory.ModelCharpoly.unitary
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:27:09.746863+00:00
-- url     : https://prove2.me/theorems/9c9c6677-0277-4032-b136-e62f52a796de
-- title:
--   Model Charpoly: unitary
-- statement:
--   The Model Charpoly construction uses the unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HermitianModelCharpolyEqAndUnitary.lean#L19-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HermitianModelCharpolyEqAndUnitary.lean#L19-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianModelCharpolyEqAndUnitary
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
open GlobalTheory GlobalTheory.ModelCharpoly
open GlobalTheory.InertUnitOrb

theorem GlobalTheory.ModelCharpoly.unitary (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (γ : Matrix (Fin n) (Fin n) K.E)
    (x : B.Aˣ) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)) (h : ∀ y, ψ (B.g * y) = γ *ᵥ ψ y)
    (hh : ∀ y z, stdH K n (ψ y) (ψ z) = B.herm x y z) (hg : B.g * B.σ B.g = 1) :
    (γ.map K.c)ᵀ * γ = 1 := by sorry
