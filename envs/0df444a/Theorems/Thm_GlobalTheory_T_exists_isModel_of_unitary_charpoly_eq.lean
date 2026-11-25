-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_isModel_of_unitary_charpoly_eq
-- name    : GlobalTheory.T.exists_isModel_of_unitary_charpoly_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:30:09.275683+00:00
-- url     : https://prove2.me/theorems/1caa622a-a727-5a08-b77f-c485abb745de
-- title:
--   T: exists is Model of unitary charpoly eq
-- statement:
--   The T construction uses the exists is Model of unitary charpoly eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIsModelOfUnitaryStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIsModelOfUnitaryStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsModelOfUnitary
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsModelOfUnitaryStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_isModel_of_unitary_charpoly_eq : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (γ : Matrix (Fin n) (Fin n) K.E), (γ.map K.c)ᵀ * γ = 1 → B.g * B.σ B.g = 1 → B.P.Separable → γ.charpoly = B.P → ∃ (x : B.Aˣ) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel B γ x ψ := by sorry
