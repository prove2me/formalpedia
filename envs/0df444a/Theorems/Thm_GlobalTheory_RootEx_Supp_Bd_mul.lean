-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Supp_Bd_mul
-- name    : GlobalTheory.RootEx.Supp.Bd.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:50:39.561874+00:00
-- url     : https://prove2.me/theorems/acf1087a-2f45-4797-a218-53fc5ba5913d
-- title:
--   Bd: mul
-- statement:
--   The Bd construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CharEqOneOfOpENeZero.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/CharEqOneOfOpENeZero.lean#L17-L23

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

theorem GlobalTheory.RootEx.Supp.Bd.mul {ι κ τ : Type} [Fintype κ] {γ δ : ValueGroupWithZero k} {x : Matrix ι κ k} {y : Matrix κ τ k}
    (hx : Bd γ x) (hy : Bd δ y) : Bd (γ * δ) (x * y) := by sorry
