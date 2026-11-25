-- Prove2me | Theorems.Thm_GlobalTheory_T_invAlg_identity_of_principal_congruence
-- name    : GlobalTheory.T.invAlg_identity_of_principal_congruence
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:34:09.223909+00:00
-- url     : https://prove2.me/theorems/c7a10f3f-1d05-53c4-a9ed-d8f61ad3d5fd
-- title:
--   T: inv Alg identity of principal congruence
-- statement:
--   The T construction uses the inv Alg identity of principal congruence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdentityOfPrincipalCongruenceStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IdentityOfPrincipalCongruenceStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityOfPrincipalCongruence
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityOfPrincipalCongruenceStatement
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

theorem GlobalTheory.T.invAlg_identity_of_principal_congruence : UnitLemmaLie → ∀ (K : UQ) (a : K.O), K.Small a → ∀ B₁ B₂ : InvAlg K, (1 + algebraMap K.O B₁.A a * B₁.g) * B₁.σ (1 + algebraMap K.O B₁.A a * B₁.g) = 1 → (1 + algebraMap K.O B₂.A a * B₂.g) * B₂.σ (1 + algebraMap K.O B₂.A a * B₂.g) = 1 → (B₁.P * B₂.P).Separable → InvAlg.Identity B₁ B₂ := by sorry
