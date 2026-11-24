-- Prove2me | Theorems.Thm_GlobalTheory_eq_zero_of_forall_residueField_functional
-- name    : GlobalTheory.eq_zero_of_forall_residueField_functional
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:19:00.550062+00:00
-- url     : https://prove2.me/theorems/2e092ce1-3fde-42f7-9594-dc6d4c96699f
-- title:
--   Global Theory: eq zero of forall residue Field functional
-- statement:
--   The Global Theory construction uses the eq zero of forall residue Field functional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqZeroOfForallResidueFieldFunctional.lean#L5-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqZeroOfForallResidueFieldFunctional.lean#L5-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfForallResidueFieldFunctional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.eq_zero_of_forall_residueField_functional (A M : Type) [CommRing A] [IsReduced A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Projective A M] (x : M)
    (hx : ∀ (p : Ideal A) [p.IsPrime] (l : M →ₗ[A] p.ResidueField), l x = 0) : x = 0 := by sorry
