-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Supp_Bd_mono
-- name    : GlobalTheory.RootEx.Supp.Bd.mono
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:29.988799+00:00
-- url     : https://prove2.me/theorems/b4bcaf2e-4bc4-48cc-9516-d42a4f287477
-- title:
--   Bd: mono
-- statement:
--   The Bd construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CharEqOneOfOpENeZero.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CharEqOneOfOpENeZero.lean#L25-L26

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

theorem GlobalTheory.RootEx.Supp.Bd.mono {ι κ : Type} {γ δ : ValueGroupWithZero k} {x : Matrix ι κ k} (hx : Bd γ x) (h : γ ≤ δ) :
    Bd δ x := by sorry
