-- Prove2me | Theorems.Thm_GlobalTheory_GoodCorank_exists_good_sat
-- name    : GlobalTheory.GoodCorank.exists_good_sat
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:33:53.407889+00:00
-- url     : https://prove2.me/theorems/63f3cee6-e3bc-4ff1-a58a-fdc87a8cd7c4
-- title:
--   Good Corank: exists good sat
-- statement:
--   The Good Corank construction uses the exists good sat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsSaturatedGoodVectorsSmallCorank.lean#L156-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsSaturatedGoodVectorsSmallCorank.lean#L156-L172

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RowDataAdaptedChainData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsSaturatedGoodVectorsSmallCorank
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
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.GoodCorank
variable {C : Type} [Field C] {V : VF C}
variable {d : ℕ} {I J : Type} [Fintype I] [DecidableEq I]

theorem GlobalTheory.GoodCorank.exists_good_sat (C : Type) [Field C] [IsAlgClosed C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J]
    [DecidableEq I] (G : Cart V d I J) (a : ZMod d) :
    ∃ (N : ℕ) (w : Fin N → I → C) (x : Fin N → ℕ → I ⊕ J → C), (∀ ν, G.Good a (w ν) (x ν)) ∧
      (∀ ν c, G.ty (Sum.inl c) ≠ a → w ν c = 0) ∧ IsSat V w ∧
      (Finset.univ.filter fun c : I => G.ty (Sum.inl c) = a).card ≤
        N + (Finset.univ.filter fun c : I => G.ty (Sum.inl c) = a + 1).card := by sorry
