-- Prove2me | Theorems.Thm_GlobalTheory_HenselZero_exists_factor_stalk
-- name    : GlobalTheory.HenselZero.exists_factor_stalk
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:53:12.537805+00:00
-- url     : https://prove2.me/theorems/c75ccce2-97aa-41f4-b45f-313a11ea8d05
-- title:
--   Hensel Zero: exists factor stalk
-- statement:
--   The Hensel Zero construction uses the exists factor stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsSectionOfTransversal.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsSectionOfTransversal.lean#L12-L15

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

theorem GlobalTheory.HenselZero.exists_factor_stalk {X : Scheme.{0}} {T : CommRingCat.{0}} [IsLocalRing T] (w : Spec T ⟶ X) {y : X}
    (hw : w (closedPoint T) = y) : ∃ χ : X.presheaf.stalk y ⟶ T, Spec.map χ ≫ X.fromSpecStalk y = w := by sorry
