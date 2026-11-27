-- Prove2me | Theorems.Thm_GlobalTheory_scheme_descends_to_subalgebra
-- name    : GlobalTheory.scheme_descends_to_subalgebra
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:05:53.051812+00:00
-- url     : https://prove2.me/theorems/6fd14225-5b5d-4194-8ce2-ae39bb836eee
-- title:
--   Global Theory: scheme descends to subalgebra
-- statement:
--   The Global Theory construction uses the scheme descends to subalgebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SchemeDescendsToSubalgebra.lean#L408-L428
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SchemeDescendsToSubalgebra.lean#L408-L428

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
open GlobalTheory

theorem GlobalTheory.scheme_descends_to_subalgebra :
    ∀ (V R : Type) [CommRing V] [CommRing R] [Algebra V R] (X : Over (Sp R)), LocallyOfFinitePresentation X.hom → QuasiCompact X.hom → IsSeparated X.hom → ∃ s : Finset R, ∀ W : Subalgebra V R, (↑s : Set R) ⊆ W → ∃ X₀ : Over (Sp W), LocallyOfFinitePresentation X₀.hom ∧ QuasiCompact X₀.hom ∧ QuasiSeparated X₀.hom ∧ Nonempty ((Over.pullback (spMap W.val.toRingHom)).obj X₀ ≅ X) := by sorry
