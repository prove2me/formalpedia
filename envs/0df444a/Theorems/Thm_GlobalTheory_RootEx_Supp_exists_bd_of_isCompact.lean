-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Supp_exists_bd_of_isCompact
-- name    : GlobalTheory.RootEx.Supp.exists_bd_of_isCompact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:49.915027+00:00
-- url     : https://prove2.me/theorems/dc0b72cb-c99f-423c-870d-24a64690f2de
-- title:
--   Supp: exists bd of is Compact
-- statement:
--   The Supp construction uses the exists bd of is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CharEqOneOfOpENeZero.lean#L49-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CharEqOneOfOpENeZero.lean#L49-L62

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

theorem GlobalTheory.RootEx.Supp.exists_bd_of_isCompact {ι κ : Type} [Finite ι] [Finite κ] {S : Set (Matrix ι κ k)} (hS : IsCompact S) :
    ∃ γ : ValueGroupWithZero k, ∀ x ∈ S, Bd γ x := by sorry
