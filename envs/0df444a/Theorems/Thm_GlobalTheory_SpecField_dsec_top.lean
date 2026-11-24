-- Prove2me | Theorems.Thm_GlobalTheory_SpecField_dsec_top
-- name    : GlobalTheory.SpecField.dsec_top
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:20:39.373174+00:00
-- url     : https://prove2.me/theorems/6306686a-e874-45ae-9ad0-847333604770
-- title:
--   Spec Field: dsec top
-- statement:
--   The Spec Field construction uses the dsec top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSpecVectorFieldOfDualNumberSection.lean#L88-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSpecVectorFieldOfDualNumberSection.lean#L88-L91

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__DenseInterior_23def473f6482931
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSpecVectorFieldOfDualNumberSection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS
noncomputable section
open GlobalTheory GlobalTheory.SpecField
open AlgebraicGeometry
variable {A : Type} [CommRing A]
variable (σ : A →+* DualNumber A) (hσ : ∀ a, (σ a).fst = a) (S : Submonoid A)

theorem GlobalTheory.SpecField.dsec_top (a : A) :
    dsec σ hσ ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (σ a).snd := by sorry
