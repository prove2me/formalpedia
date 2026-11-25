-- Prove2me | Theorems.Thm_GlobalTheory_AdaptedChain_chain
-- name    : GlobalTheory.AdaptedChain.chain
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:25:03.011845+00:00
-- url     : https://prove2.me/theorems/5f6f3130-fd81-4c4c-9883-a9a88bd1a616
-- title:
--   Adapted Chain: chain
-- statement:
--   The Adapted Chain construction uses the chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/RowDataAdaptedChainData.lean#L383-L482
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/RowDataAdaptedChainData.lean#L383-L482

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RowDataAdaptedChainData
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.AdaptedChain
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
variable {X : Cart V d I J}

theorem GlobalTheory.AdaptedChain.chain [IsAlgClosed C] (j' : ℕ) (K : ℕ) : (∀ s, 0 < s → s < K → ((2 * s : ℕ) : ZMod d) ≠ 0) →
    ∀ (a : ZMod d), (∀ s < K, (Finset.univ.filter fun k =>
      X.ty (Sum.inl k) = a + ((2 * s : ℕ) : ZMod d) + 1).card ≤ j') →
    ∀ (S : Sys X) (Q : Finset I), (∀ c ∈ Q, X.ty (Sum.inl c) = a) →
    ∀ (L : AddSubgroup (I → C)), Stable V L → (∀ c ∈ Q, S.tan c ∈ L) →
    ∃ (S' : Sys X) (lev : I → ℕ),
      (∀ c, (∀ s < K, X.ty (Sum.inl c) ≠ a + ((2 * s : ℕ) : ZMod d)) → S'.cur c = S.cur c) ∧
      (∀ c, lev c < K → X.ty (Sum.inl c) = a + ((2 * lev c : ℕ) : ZMod d) ∧
        ∀ k, S'.cur c 1 (Sum.inl k) = 0) ∧
      (∀ c ∈ Q, lev c = 0 → S'.tan c ∈ L) ∧
      Q.card ≤ (Q.filter fun c => lev c = 0).card + K * j' ∧
      ∀ c, lev c + 1 < K → ∃ g lam : I → C, (∀ e, V.Ge 0 (g e)) ∧ (∀ e, V.Ge 0 (lam e)) ∧
        (∀ e, lev e ≠ lev c + 1 → g e = 0) ∧
        ∀ k, (V.l : C) * S'.cur c 2 (Sum.inl k) = ∑ e, g e * S'.tan e k + (V.l : C) * lam k := by sorry
