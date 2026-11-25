-- Prove2me | Theorems.Thm_GlobalTheory_T_powerSemilinear_rank_nullity_mod_maxIdeal
-- name    : GlobalTheory.T.powerSemilinear_rank_nullity_mod_maxIdeal
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:36:50.037966+00:00
-- url     : https://prove2.me/theorems/25f86ec4-9bab-47ac-843c-3ce05d543505
-- title:
--   T: power Semilinear rank nullity mod max Ideal
-- statement:
--   The T construction uses the power Semilinear rank nullity mod max Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PowerSemilinearRankNullityModMaxIdealStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PowerSemilinearRankNullityModMaxIdealStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowerSemilinearRankNullityModMaxIdeal
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowerSemilinearRankNullityModMaxIdealStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.powerSemilinear_rank_nullity_mod_maxIdeal : ∀ (C : Type) [Field C] [IsAlgClosed C] (V : VF C) (σ : Type) (m k Q : ℕ), 1 ≤ Q → ∀ Y : Fin m → σ → C, (∀ δ x, V.Ge 0 (Y δ x)) → (∀ (N : ℕ) (x : Fin N → Fin m → C), (∀ ν δ, V.Ge 0 (x ν δ)) → IndepMod V x → (∀ ν s, V.MM (∑ δ, x ν δ ^ Q * Y δ s)) → N ≤ k) → ∃ (m' : ℕ) (cc : Fin m' ↪ Fin m), m ≤ m' + k ∧ IndepMod V (fun ν => Y (cc ν)) := by sorry
