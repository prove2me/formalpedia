-- Prove2me | Theorems.Thm_GlobalTheory_T_two_pow_le_index_localNormsSqrtExtension
-- name    : GlobalTheory.T.two_pow_le_index_localNormsSqrtExtension
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T15:37:33.469798+00:00
-- url     : https://prove2.me/theorems/a6d4f396-824c-4eb3-8410-4296b160caaa
-- title:
--   T: two pow le index local Norms Sqrt Extension
-- statement:
--   The T construction uses the two pow le index local Norms Sqrt Extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/TwoPowLeIndexLocalNormsSqrtExtensionStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/TwoPowLeIndexLocalNormsSqrtExtensionStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TwoPowLeIndexLocalNormsSqrtExtension
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TwoPowLeIndexLocalNormsSqrtExtensionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.two_pow_le_index_localNormsSqrtExtension : ∀ (F : Type) [Field F] [NumberField F] (δ : F) (S : Finset (HeightOneSpectrum (𝓞 F))), δ ≠ 0 → (locNorm F δ S).index ≠ 0 ∧ 2 ^ (tFin F δ S + tReal F δ) ≤ (locNorm F δ S).index := by sorry
