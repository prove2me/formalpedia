-- Prove2me | Theorems.Thm_GlobalTheory_IwahoriFactor_iwahori_factorisation
-- name    : GlobalTheory.IwahoriFactor.iwahori_factorisation
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:11:43.677868+00:00
-- url     : https://prove2.me/theorems/9f73da87-caae-4dff-80a4-9f8c02d25764
-- title:
--   Iwahori Factor: iwahori factorisation
-- statement:
--   The Iwahori Factor construction uses the iwahori factorisation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvdInvOfBlockTriangular.lean#L251-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvdInvOfBlockTriangular.lean#L251-L253

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UdlApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IwahoriFactorisation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvdInvOfBlockTriangular
import Theorems.Thm_GlobalTheory_UnipotentBorder_iwahori_factorisation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.IwahoriFactor

theorem GlobalTheory.IwahoriFactor.iwahori_factorisation : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (n r s : ℕ), 1 ≤ s → ∀ g : GL (Fin n) O, (∀ i j, (i < j → ϖ ^ r ∣ (g : Matrix (Fin n) (Fin n) O) i j) ∧ (j < i → ϖ ^ s ∣ (g : Matrix (Fin n) (Fin n) O) i j)) → ∃! p : Matrix (Fin n) (Fin n) O × (Fin n → Oˣ) × Matrix (Fin n) (Fin n) O, (∀ i j, (j < i → p.1 i j = 0) ∧ (i = j → p.1 i j = 1) ∧ (i < j → ϖ ^ r ∣ p.1 i j)) ∧ (∀ i j, (i < j → p.2.2 i j = 0) ∧ (i = j → p.2.2 i j = 1) ∧ (j < i → ϖ ^ s ∣ p.2.2 i j)) ∧ (g : Matrix (Fin n) (Fin n) O) = p.1 * Matrix.diagonal (fun i => (p.2.1 i : O)) * p.2.2 := by sorry
