-- Prove2me | Theorems.Thm_GlobalTheory_InertUnitOrb_exists_isModel_of_unitary
-- name    : GlobalTheory.InertUnitOrb.exists_isModel_of_unitary
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:16:13.592718+00:00
-- url     : https://prove2.me/theorems/10939166-5de6-45b5-948b-52fe00a1bc39
-- title:
--   Inert Unit Orb: exists is Model of unitary
-- statement:
--   The Inert Unit Orb construction uses the exists is Model of unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIsModelOfUnitary.lean#L18-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIsModelOfUnitary.lean#L18-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfSeparable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsModelOfUnitary
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

theorem GlobalTheory.InertUnitOrb.exists_isModel_of_unitary : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (γ : Matrix (Fin n) (Fin n) K.E), (γ.map K.c)ᵀ * γ = 1 → B.g * B.σ B.g = 1 → B.P.Separable → γ.charpoly = B.P → ∃ (x : B.Aˣ) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel B γ x ψ := by sorry
