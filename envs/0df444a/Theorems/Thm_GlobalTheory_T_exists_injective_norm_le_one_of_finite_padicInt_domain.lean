-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_injective_norm_le_one_of_finite_padicInt_domain
-- name    : GlobalTheory.T.exists_injective_norm_le_one_of_finite_padicInt_domain
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:36:08.387834+00:00
-- url     : https://prove2.me/theorems/53732b08-3774-46cf-bc5c-4cad94e5308b
-- title:
--   T: exists injective norm le one of finite padic Int domain
-- statement:
--   The T construction uses the exists injective norm le one of finite padic Int domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInjectiveNormLeOneOfFinitePadicIntDomainStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInjectiveNormLeOneOfFinitePadicIntDomainStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInjectiveNormLeOneOfFinitePadicIntDomain
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInjectiveNormLeOneOfFinitePadicIntDomainStatement
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

theorem GlobalTheory.T.exists_injective_norm_le_one_of_finite_padicInt_domain : ∀ (p : ℕ) [Fact p.Prime] (D : Type) [CommRing D] [IsDomain D] [Algebra ℤ_[p] D] [Module.Finite ℤ_[p] D], (p : D) ≠ 0 → ∃ φ : D →+* PadicAlgCl p, Function.Injective φ ∧ ∀ d, ‖φ d‖ ≤ 1 := by sorry
