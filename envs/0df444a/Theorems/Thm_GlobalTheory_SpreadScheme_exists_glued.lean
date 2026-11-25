-- Prove2me | Theorems.Thm_GlobalTheory_SpreadScheme_exists_glued
-- name    : GlobalTheory.SpreadScheme.exists_glued
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T15:04:16.501994+00:00
-- url     : https://prove2.me/theorems/c90a2539-e549-418a-9e34-0499414f543b
-- title:
--   Spread Scheme: exists glued
-- statement:
--   The Spread Scheme construction uses the exists glued property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SchemeDescendsToSubalgebra.lean#L204-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SchemeDescendsToSubalgebra.lean#L204-L259

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
attribute [instance] PairModel.lfp PairModel.qs PairModel.qc PairModel.opn PairModel.qca
variable {S S₁ S₀ U T : Scheme.{0}} {f : S ⟶ S₀} {p : U ⟶ S} {a : T ⟶ U}

theorem GlobalTheory.SpreadScheme.exists_glued {X W : Scheme.{0}} (q : X ⟶ S) {u : U ⟶ X} {v : W ⟶ X} [IsOpenImmersion u] [IsOpenImmersion v]
    {b : T ⟶ W} (h : IsPullback a b u v) (hc : ∀ x : X, x ∈ Set.range u ∨ x ∈ Set.range v)
    (M : PairModel f (u ≫ q) a) (N : PairModel f (v ≫ q) b) (e : M.T₀ ≅ N.T₀) (he : M.τ ≫ e.hom = N.τ)
    (he' : e.hom ≫ N.a₀ ≫ N.p₀ = M.a₀ ≫ M.p₀) [CompactSpace S₀] [QuasiSeparatedSpace S₀] :
    ∃ (X₀ : Scheme.{0}) (q₀ : X₀ ⟶ S₀) (φ : X ⟶ X₀), LocallyOfFinitePresentation q₀ ∧ QuasiCompact q₀ ∧ IsPullback φ q q₀ f := by sorry
