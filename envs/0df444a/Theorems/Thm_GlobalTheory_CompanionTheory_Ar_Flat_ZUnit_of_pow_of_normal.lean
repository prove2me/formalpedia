-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Flat_ZUnit_of_pow_of_normal
-- name    : GlobalTheory.CompanionTheory.Ar.Flat.ZUnit.of_pow_of_normal
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:59:48.224496+00:00
-- url     : https://prove2.me/theorems/e4232039-3075-4ea6-9d99-2a5e2f7d9ac0
-- title:
--   ZUnit: of pow of normal
-- statement:
--   The ZUnit construction uses the of pow of normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsGenOfIsVBOne.lean#L63-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsGenOfIsVBOne.lean#L63-L64

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

theorem GlobalTheory.CompanionTheory.Ar.Flat.ZUnit.of_pow_of_normal (hN : NormalCpt ξ) {n : ℕ} (hn : n ≠ 0) (h : unitAt ξ p (a ^ n)) : unitAt ξ p a := by sorry
