-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Flat_orderAt_one_zero
-- name    : GlobalTheory.CompanionTheory.Ar.Flat.orderAt_one_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:59:12.571856+00:00
-- url     : https://prove2.me/theorems/d7a95008-bf75-4278-9eb0-7080aaabf6cc
-- title:
--   Flat: order At one zero
-- statement:
--   The Flat construction uses the order At one zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsGenOfIsVBOne.lean#L145-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsGenOfIsVBOne.lean#L145-L155

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

theorem GlobalTheory.CompanionTheory.Ar.Flat.orderAt_one_zero : OrderAt L σ ϖ 1 0 p ↔ σ ≠ 0 ∧ L p = Submodule.span (regAt ξ p) {σ} := by sorry
