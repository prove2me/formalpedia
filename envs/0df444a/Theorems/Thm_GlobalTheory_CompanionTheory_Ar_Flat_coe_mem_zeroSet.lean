-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Flat_coe_mem_zeroSet
-- name    : GlobalTheory.CompanionTheory.Ar.Flat.coe_mem_zeroSet
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:18:16.942922+00:00
-- url     : https://prove2.me/theorems/843b7f9a-5957-4e12-a077-de39a644ee36
-- title:
--   Flat: coe mem zero Set
-- statement:
--   The Flat construction uses the coe mem zero Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsGenOfIsVBOne.lean#L84-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/ExistsGenOfIsVBOne.lean#L84-L85

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

theorem GlobalTheory.CompanionTheory.Ar.Flat.coe_mem_zeroSet {ϖ : Ω} (p : Cpt ξ) : p.1 ∈ zeroSet ξ ϖ ↔ ¬ unitAt ξ p ϖ := by sorry
