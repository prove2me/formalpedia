-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Supp_isCompact_bd
-- name    : GlobalTheory.RootEx.Supp.isCompact_bd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:53.118225+00:00
-- url     : https://prove2.me/theorems/fd0fed18-9ee3-4cba-9009-acca8a8620b2
-- title:
--   Supp: is Compact bd
-- statement:
--   The Supp construction uses the is Compact bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CharEqOneOfOpENeZero.lean#L82-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CharEqOneOfOpENeZero.lean#L82-L101

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

theorem GlobalTheory.RootEx.Supp.isCompact_bd {ι : Type} [Fintype ι] [DecidableEq ι] (γ : ValueGroupWithZero k) :
    IsCompact {g : GL ι k | Bd γ g.val ∧ Bd γ (g⁻¹).val} := by sorry
