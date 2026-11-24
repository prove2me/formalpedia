-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_IsUWeilPair_isWeilPair
-- name    : GlobalTheory.WeilM.IsUWeilPair.isWeilPair
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:54:10.642799+00:00
-- url     : https://prove2.me/theorems/b7004fd9-f1b3-4fb8-99a9-ea29a53486f1
-- title:
--   Is UWeil Pair: is Weil Pair
-- statement:
--   The Is UWeil Pair construction uses the is Weil Pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L453-L455
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L453-L455

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped NNReal Classical
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
variable {c}
variable (c)
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable [Invertible (2 : R)]
variable [TopologicalSpace R] [TopologicalSpace E]
variable {c} [IsModuleTopology R E] {C : TestClass R} {ψ : AddChar R ℂ} {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E}
  {κ : Type} [Fintype κ] {d : Darboux (symp c ξ JA JB) κ}
variable {χA χB : Eˣ →* Circle} {om : UG c JA × UG c JB →* Module.End ℂ ((κ → R) → ℂ)}

theorem GlobalTheory.WeilM.IsUWeilPair.isWeilPair (h : IsUWeilPair c C ψ ξ JA JB d χA χB om) : IsWeilPair c C ψ ξ JA JB d χA χB om := by sorry
