-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Flat_OrderAt_mul_nat
-- name    : GlobalTheory.CompanionTheory.Ar.Flat.OrderAt.mul_nat
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:18:06.529417+00:00
-- url     : https://prove2.me/theorems/ff2edabe-7185-4a8d-92bf-c3f81d179e84
-- title:
--   Order At: mul nat
-- statement:
--   The Order At construction uses the mul nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsGenOfIsVBOne.lean#L157-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsGenOfIsVBOne.lean#L157-L161

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EtaleLocalizationAtPrimeTensorOfLowHeight
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsGenOfIsVBOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]
variable {L : Lat ξ E} {σ : E} {ϖ : Ω} {M M' : ℕ} {a a' : ℤ} {p : Cpt ξ}

theorem GlobalTheory.CompanionTheory.Ar.Flat.OrderAt.mul_nat (h : OrderAt L σ ϖ M a p) (k : ℕ) : OrderAt L σ ϖ (M * k) (a * k) p := by sorry
