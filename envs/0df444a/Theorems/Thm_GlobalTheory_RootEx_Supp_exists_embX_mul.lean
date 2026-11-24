-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Supp_exists_embX_mul
-- name    : GlobalTheory.RootEx.Supp.exists_embX_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:57.615059+00:00
-- url     : https://prove2.me/theorems/f6746d8a-b742-4ff2-996f-10466193abcb
-- title:
--   Supp: exists emb X mul
-- statement:
--   The Supp construction uses the exists emb X mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CharEqOneOfOpENeZero.lean#L174-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CharEqOneOfOpENeZero.lean#L174-L210

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Supp

theorem GlobalTheory.RootEx.Supp.exists_embX_mul {k : Type} [Field k] [ValuativeRel k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (m : GL (n ⊕ Fin c) k) (h0 : ∀ i s, m.val (Sum.inr i) (Sum.inl s) = 0) {γ : ValueGroupWithZero k}
    (hγ : 1 ≤ γ) (h1 : ∀ i j, valuation k (m.val (Sum.inr i) (Sum.inr j)) ≤ γ)
    (h2 : ∀ r j, valuation k ((m⁻¹).val r (Sum.inr j)) ≤ γ) :
    ∃ (x : GL n k) (w : GL (n ⊕ Fin c) k), m = embX c x * w ∧ Bd (γ * γ) w.val ∧ Bd (γ * γ) (w⁻¹).val := by sorry
