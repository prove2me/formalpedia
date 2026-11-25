-- Prove2me | Theorems.Thm_GlobalTheory_SpreadScheme_exists_up_comp_up
-- name    : GlobalTheory.SpreadScheme.exists_up_comp_up
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:04:00.504943+00:00
-- url     : https://prove2.me/theorems/92b9796e-d0b7-448a-bb41-0215c27a3143
-- title:
--   Spread Scheme: exists up comp up
-- statement:
--   The Spread Scheme construction uses the exists up comp up property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SchemeDescendsToSubalgebra.lean#L60-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SchemeDescendsToSubalgebra.lean#L60-L90

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GlueModelsOverSubfield
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SchemeDescendsToSubalgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SpreadScheme
open GlobalTheory.Spread GlobalTheory.GlueModels
variable {k V : Type} [CommRing k] [CommRing V] [Algebra k V] {P Q T : Scheme.{0}}
  {p : P ⟶ Sp k} {q : Q ⟶ Sp k} {t : T ⟶ Sp V} {τ : T ⟶ P} {τ' : T ⟶ Q}

theorem GlobalTheory.SpreadScheme.exists_up_comp_up [LocallyOfFiniteType p] [QuasiCompact p]
    (hτ : IsPullback τ t p (spMap (algebraMap k V)))
    (hτ' : IsPullback τ' t q (spMap (algebraMap k V))) {R₁ R₂ : Subalgebra k V} (hR₁ : R₁.FG) (hR₂ : R₂.FG)
    (ψ : pullback p (spMap (algebraMap k R₁)) ⟶ Q) (hψ : ψ ≫ q = pullback.fst _ _ ≫ p)
    (χ : pullback q (spMap (algebraMap k R₂)) ⟶ P) (hχ : χ ≫ p = pullback.fst _ _ ≫ q)
    (hψ' : bcMap p R₁.val ≫ ψ = hτ.isoPullback.inv ≫ τ')
    (hχ' : bcMap q R₂.val ≫ χ = hτ'.isoPullback.inv ≫ τ) :
    ∃ R : Subalgebra k V, R.FG ∧ ∀ (R' : Subalgebra k V) (h₁ : R₁ ≤ R') (h₂ : R₂ ≤ R'), R ≤ R' →
      up h₁ ψ hψ ≫ up h₂ χ hχ = 𝟙 _ := by sorry
