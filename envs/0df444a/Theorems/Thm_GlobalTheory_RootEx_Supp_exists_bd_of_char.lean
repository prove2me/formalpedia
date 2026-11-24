-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Supp_exists_bd_of_char
-- name    : GlobalTheory.RootEx.Supp.exists_bd_of_char
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:00.370961+00:00
-- url     : https://prove2.me/theorems/78a2f809-4f8e-4bb9-830b-1dd63facc5f5
-- title:
--   Supp: exists bd of char
-- statement:
--   The Supp construction uses the exists bd of char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CharEqOneOfOpENeZero.lean#L104-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CharEqOneOfOpENeZero.lean#L104-L123

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
variable {k : Type} [Field k] [ValuativeRel k]
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.RootEx.Supp.exists_bd_of_char (ψ : AddChar k Circle) (hψ : ψ ≠ 1) (u : kˣ) :
    ∃ γ : ValueGroupWithZero k, ∀ a : k,
      (∀ t, valuation k t ≤ valuation k (u : k) → ψ (a * t) = 1) → valuation k a ≤ γ := by sorry
