-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_dominating_local_domain_eq_mul_maximal
-- name    : GlobalTheory.T.exists_dominating_local_domain_eq_mul_maximal
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:29:05.561872+00:00
-- url     : https://prove2.me/theorems/145912d3-b703-4511-8623-8925d9131c93
-- title:
--   T: exists dominating local domain eq mul maximal
-- statement:
--   The T construction uses the exists dominating local domain eq mul maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDominatingLocalDomainEqMulMaximalStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDominatingLocalDomainEqMulMaximalStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDominatingLocalDomainEqMulMaximal
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDominatingLocalDomainEqMulMaximalStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_dominating_local_domain_eq_mul_maximal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (f G : R), G ∉ Ideal.span {f} → ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsLocalRing B) (_ : IsNoetherianRing B) (ι : R →+* B), Function.Injective ι ∧ IsLocalHom ι ∧ (∀ b : B, ∃ r : R, b - ι r ∈ maximalIdeal B) ∧ ∃ u ∈ maximalIdeal B, ι f = ι G * u := by sorry
