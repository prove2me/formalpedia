-- Prove2me | Theorems.Thm_GlobalTheory_T_fullLattice_sandwich_between_integral_elements
-- name    : GlobalTheory.T.fullLattice_sandwich_between_integral_elements
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:40:54.674801+00:00
-- url     : https://prove2.me/theorems/6a467396-a653-483a-bb30-efc91f4c4ec9
-- title:
--   T: full Lattice sandwich between integral elements
-- statement:
--   The T construction uses the full Lattice sandwich between integral elements property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FullLatticeSandwichBetweenIntegralElementsStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FullLatticeSandwichBetweenIntegralElementsStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullLatticeSandwichBetweenIntegralElements
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullLatticeSandwichBetweenIntegralElementsStatement
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

theorem GlobalTheory.T.fullLattice_sandwich_between_integral_elements : ∀ (K : UQ) (B : InvAlg K), B.LieReg → ∀ a : K.O, K.Small a → ∀ L : Submodule K.O B.A, IsLat K.O K.E L → ∃ m : ℕ, ∀ n : ℕ, m ≤ n → (∀ y : B.A, IsIntegral K.O y → algebraMap K.O B.A a ^ n * y ∈ L) ∧ ∀ y ∈ L, IsIntegral K.O (algebraMap K.O B.A a ^ n * y) := by sorry
