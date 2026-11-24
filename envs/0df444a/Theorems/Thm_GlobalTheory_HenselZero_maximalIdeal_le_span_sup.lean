-- Prove2me | Theorems.Thm_GlobalTheory_HenselZero_maximalIdeal_le_span_sup
-- name    : GlobalTheory.HenselZero.maximalIdeal_le_span_sup
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:54:15.98856+00:00
-- url     : https://prove2.me/theorems/1594123f-24d9-40d1-a351-b79fac182618
-- title:
--   Hensel Zero: maximal Ideal le span sup
-- statement:
--   The Hensel Zero construction uses the maximal Ideal le span sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsSectionOfTransversal.lean#L53-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsSectionOfTransversal.lean#L53-L84

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
variable {O : Type} [CommRing O] [IsLocalRing O] {X Y : Scheme.{0}} {p : X ⟶ Sp O} {q : Y ⟶ Sp (ResidueField O)}
  {φ : Y ⟶ X} (hφ : IsPullback φ q p (spMap (residue O)))
include hφ

theorem GlobalTheory.HenselZero.maximalIdeal_le_span_sup {ι : Type} (y : Y) (α : CommRingCat.of O ⟶ X.presheaf.stalk (φ y))
    (hα : Spec.map α = X.fromSpecStalk (φ y) ≫ p) (f : ι → X.presheaf.stalk (φ y))
    (h : maximalIdeal _ ≤ Ideal.span (Set.range fun i => (φ.stalkMap y).hom (f i))) :
    maximalIdeal _ ≤ Ideal.span (Set.range f) ⊔ (maximalIdeal O).map α.hom := by sorry
