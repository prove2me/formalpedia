-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Flat_ZUnit_of_pow
-- name    : GlobalTheory.CompanionTheory.Ar.Flat.ZUnit.of_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:48:40.172863+00:00
-- url     : https://prove2.me/theorems/9544864c-27f9-495d-8a1a-f5fc9d0da961
-- title:
--   ZUnit: of pow
-- statement:
--   The ZUnit construction uses the of pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsGenOfIsVBOne.lean#L56-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsGenOfIsVBOne.lean#L56-L58

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
open GlobalTheory.CompanionTheory.Ar.Flat.ZUnit
variable {p : Cpt ξ} {a b : Ω}

theorem GlobalTheory.CompanionTheory.Ar.Flat.ZUnit.of_pow (ha : a ∈ regAt ξ p) {n : ℕ} (hn : n ≠ 0) (h : unitAt ξ p (a ^ n)) : unitAt ξ p a := by sorry
