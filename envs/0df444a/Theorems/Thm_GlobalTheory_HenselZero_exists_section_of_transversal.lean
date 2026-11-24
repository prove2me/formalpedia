-- Prove2me | Theorems.Thm_GlobalTheory_HenselZero_exists_section_of_transversal
-- name    : GlobalTheory.HenselZero.exists_section_of_transversal
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:56:48.768419+00:00
-- url     : https://prove2.me/theorems/cbc96912-fc6d-4eb4-9ac4-8f6e31c960d5
-- title:
--   Hensel Zero: exists section of transversal
-- statement:
--   The Hensel Zero construction uses the exists section of transversal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsSectionOfTransversal.lean#L88-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsSectionOfTransversal.lean#L88-L159

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FormallySmoothQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_JacNeZeroIffSpanEqMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsSectionOfTransversal
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

theorem GlobalTheory.HenselZero.exists_section_of_transversal {O ι : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Fintype ι] [DecidableEq ι] {X Y : Scheme.{0}} {p : X ⟶ Sp O} [Smooth p]
    {q : Y ⟶ Sp (ResidueField O)} {φ : Y ⟶ X} (hφ : IsPullback φ q p (spMap (residue O)))
    (t : Sp (ResidueField O) ⟶ Y) (ht : t ≫ q = 𝟙 _) (pt : Sp (ResidueField O)) {U : X.Opens} (hU : φ (t pt) ∈ U)
    (f : ι → Γ(X, U)) (hf : ∀ i, valT (t ≫ φ) U (f i) = 0)
    (hm : maximalIdeal _ ≤ Ideal.span (Set.range fun i => gs φ (t pt) U (f i)))
    (w : ι → (Sp (DualNumber (ResidueField O)) ⟶ Y))
    (hw₁ : ∀ k, spMap (TrivSqZeroExt.fstHom (ResidueField O) (ResidueField O) (ResidueField O)).toRingHom ≫ w k = t)
    (hw₂ : ∀ k, w k ≫ q = spMap (algebraMap _ _))
    (hd : (Matrix.of fun i k => (valT (w k ≫ φ) U (f i)).snd).det ≠ 0) :
    ∃ z : Sp O ⟶ X, z ≫ p = 𝟙 _ ∧ spMap (residue O) ≫ z = t ≫ φ ∧ (∀ i, valT z U (f i) = 0) ∧
      ∀ y, y ⤳ φ (t pt) → (∀ i, y ∉ X.basicOpen (f i)) → ∃ r, z r = y := by sorry
