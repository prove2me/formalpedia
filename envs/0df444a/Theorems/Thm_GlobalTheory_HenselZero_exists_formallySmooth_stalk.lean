-- Prove2me | Theorems.Thm_GlobalTheory_HenselZero_exists_formallySmooth_stalk
-- name    : GlobalTheory.HenselZero.exists_formallySmooth_stalk
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:53:33.951413+00:00
-- url     : https://prove2.me/theorems/81522979-270d-466c-9c91-46bfd7e580fe
-- title:
--   Hensel Zero: exists formally Smooth stalk
-- statement:
--   The Hensel Zero construction uses the exists formally Smooth stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsSectionOfTransversal.lean#L17-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsSectionOfTransversal.lean#L17-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FormallySmoothQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_JacNeZeroIffSpanEqMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsSectionOfTransversal
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.HenselZero

theorem GlobalTheory.HenselZero.exists_formallySmooth_stalk {O : CommRingCat.{0}} {X : Scheme.{0}} (p : X ⟶ Spec O) [Smooth p] (y : X) :
    ∃ α : O ⟶ X.presheaf.stalk y, α.hom.FormallySmooth ∧ Spec.map α = X.fromSpecStalk y ≫ p := by sorry
