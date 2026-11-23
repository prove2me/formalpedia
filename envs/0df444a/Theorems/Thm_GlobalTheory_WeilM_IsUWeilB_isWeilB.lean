-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_IsUWeilB_isWeilB
-- name    : GlobalTheory.WeilM.IsUWeilB.isWeilB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:51.642297+00:00
-- url     : https://prove2.me/theorems/68b01190-1409-4b60-a41b-ddbde17dc5ca
-- title:
--   Is UWeil B: is Weil B
-- statement:
--   The Is UWeil B construction uses the is Weil B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L446-L449
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/HilbertNinetyQuotientHomEqIff.lean#L446-L449

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

theorem GlobalTheory.WeilM.IsUWeilB.isWeilB {χ : Eˣ →* Circle} {om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)}
    (h : IsUWeilB c C ψ ξ JA JB d χ om) : IsWeilB c C ψ ξ JA JB d χ om := by sorry
