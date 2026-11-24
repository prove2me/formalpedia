-- Prove2me | Theorems.Thm_GlobalTheory_SpecField_exists_isField
-- name    : GlobalTheory.SpecField.exists_isField
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:21:07.375072+00:00
-- url     : https://prove2.me/theorems/0da904ca-7d48-41c5-a442-13489acd638a
-- title:
--   Spec Field: exists is Field
-- statement:
--   The Spec Field construction uses the exists is Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSpecVectorFieldOfDualNumberSection.lean#L95-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSpecVectorFieldOfDualNumberSection.lean#L95-L99

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

theorem GlobalTheory.SpecField.exists_isField (A : Type) [CommRing A] (σ : A →+* DualNumber A) (hσ : ∀ a, (σ a).fst = a) :
    ∃ d : ∀ O : (Sp A).Opens, Γ(Sp A, O) → Γ(Sp A, O), IsField ⊤ d ∧
      ∀ a : A, d ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) =
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (σ a).snd := by sorry
