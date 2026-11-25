-- Prove2me | Theorems.Thm_GlobalTheory_SpreadScheme_models_iso
-- name    : GlobalTheory.SpreadScheme.models_iso
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:16:08.933892+00:00
-- url     : https://prove2.me/theorems/af544638-d2c2-5ded-8098-b659b2376aa8
-- title:
--   Spread Scheme: models iso
-- statement:
--   The Spread Scheme construction uses the models iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SchemeDescendsToSubalgebra.lean#L92-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SchemeDescendsToSubalgebra.lean#L92-L113

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

theorem GlobalTheory.SpreadScheme.models_iso [LocallyOfFinitePresentation p] [QuasiSeparated p] [QuasiCompact p]
    [LocallyOfFinitePresentation q] [QuasiSeparated q] [QuasiCompact q]
    (hτ : IsPullback τ t p (spMap (algebraMap k V))) (hτ' : IsPullback τ' t q (spMap (algebraMap k V))) :
    ∃ (R : Subalgebra k V) (e : pullback p (spMap (algebraMap k R)) ≅ pullback q (spMap (algebraMap k R))),
      R.FG ∧ e.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧
      ∀ σ : T ⟶ pullback p (spMap (algebraMap k R)), σ ≫ pullback.fst _ _ = τ →
        σ ≫ pullback.snd _ _ = t ≫ spMap R.val.toRingHom → σ ≫ e.hom ≫ pullback.fst _ _ = τ' := by sorry
