-- Prove2me | Theorems.Thm_GlobalTheory_T_torus_mod_integralUnits_structure_and_integrality
-- name    : GlobalTheory.T.torus_mod_integralUnits_structure_and_integrality
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:35:36.261591+00:00
-- url     : https://prove2.me/theorems/d6169629-81db-4919-b051-088a4aa5a4ba
-- title:
--   T: torus mod integral Units structure and integrality
-- statement:
--   The T construction uses the torus mod integral Units structure and integrality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TorusModIntegralUnitsStructureAndIntegralityStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TorusModIntegralUnitsStructureAndIntegralityStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorusModIntegralUnitsStructureAndIntegrality
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorusModIntegralUnitsStructureAndIntegralityStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.torus_mod_integralUnits_structure_and_integrality : ∀ (K : UQ) (B : InvAlg K), B.LieReg → ∀ a : K.O, K.Small a → ∃ (r : ℕ) (φ : B.T →* Multiplicative (Fin r → ℤ)) (c : Fin r → ℕ), Function.Surjective φ ∧ (∀ t : B.T, φ t = 1 ↔ (t : B.Aˣ) ∈ intUnits K.O B.A) ∧ (∀ i, 0 < c i) ∧ ∀ (t : B.T) (k : ℕ), IsIntegral K.O ((((t : B.Aˣ)⁻¹ : B.Aˣ) : B.A) * algebraMap K.O B.A a ^ k) ↔ ∀ i, |Multiplicative.toAdd (φ t) i| ≤ ((k * c i : ℕ) : ℤ) := by sorry
