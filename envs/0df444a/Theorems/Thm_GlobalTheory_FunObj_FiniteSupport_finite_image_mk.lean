-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_FiniteSupport_finite_image_mk
-- name    : GlobalTheory.FunObj.FiniteSupport.finite_image_mk
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:42:53.476167+00:00
-- url     : https://prove2.me/theorems/ff8c1979-831d-4ce2-a079-3a16a55f6006
-- title:
--   Finite Support: finite image mk
-- statement:
--   The Finite Support construction uses the finite image mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteUnfSupportOfNeOne.lean#L347-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteUnfSupportOfNeOne.lean#L347-L355

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierJacobiUnipotentEqProdRootExchange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteUnfSupportOfNeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.FiniteSupport
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.RootEx.Supp GlobalTheory.RootEx.FJUnipotent

theorem GlobalTheory.FunObj.FiniteSupport.finite_image_mk {A : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] (H U : Subgroup A)
    (hU : IsOpen (U : Set A)) {Ω : Set A} (hΩ : IsCompact Ω) : (DoubleCoset.mk H U '' Ω).Finite := by sorry
