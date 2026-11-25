-- Prove2me | Theorems.Thm_GlobalTheory_SesqAsym_sesq_asym
-- name    : GlobalTheory.SesqAsym.sesq_asym
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:54:14.272035+00:00
-- url     : https://prove2.me/theorems/d71fdf6c-e030-42ec-836a-ee01559bb23a
-- title:
--   Sesq Asym: sesq asym
-- statement:
--   The Sesq Asym construction uses the sesq asym property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SesqAsym.lean#L15-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SesqAsym.lean#L15-L124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsAevalEqOfCharpolySeparableInvolutionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTraceMulOfSeparableGeneratedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitSigmaEqMulHilbert90InvAlgStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SesqAsym
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.SesqAsym

theorem GlobalTheory.SesqAsym.sesq_asym : ∀ (K : UQ) (B : InvAlg K), B.g * B.σ B.g = 1 → B.P.Separable → ∀ (ε : B.A), (ε = 1 ∨ ε = -1) → (∃ β : B.Aˣ, B.σ (β : B.A) = β * (ε * B.g)) ∧ ∀ (s : B.A → B.A → K.E), (∀ x y z, s (x + y) z = s x z + s y z) → (∀ (c : K.E) x z, s (c • x) z = c * s x z) → (∀ y, (∀ z, s y z = 0) → y = 0) → (∀ y z, K.c (s z y) = s (ε * B.g * y) z) → ∃ β : B.Aˣ, B.σ (β : B.A) = β * (ε * B.g) ∧ ∀ y z, s y z = B.herm β y z := by sorry
