-- Prove2me | Theorems.Thm_GlobalTheory_SS_WeakNeronEx_exists_affine
-- name    : GlobalTheory.SS.WeakNeronEx.exists_affine
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:11:10.063954+00:00
-- url     : https://prove2.me/theorems/290739f9-6dcd-480f-a072-ce3d6942fa59
-- title:
--   Weak Neron Ex: exists affine
-- statement:
--   The Weak Neron Ex construction uses the exists affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsWeakNeronModel.lean#L193-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsWeakNeronModel.lean#L193-L247

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmoothFlatAlgebraFiniteCoverDecompStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSchemeModelOfAffineSmoothChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCoverModelIrreducibleSpecialFibreStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsWeakNeronModel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.WeakNeronEx
open GlobalTheory.AbLaw ReciprocityTheory.ChartRestriction.G.Out

theorem GlobalTheory.SS.WeakNeronEx.exists_affine (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {X : Scheme.{0}} (f : X ⟶ Sp K) (hf : IsProjBy f) :
    ∃ (m : ℕ) (B : Fin m → Type) (_ : ∀ i, CommRing (B i)) (_ : ∀ i, Algebra R (B i))
      (u : ∀ i, Sp (TensorProduct R K (B i)) ⟶ X),
      (∀ i, Algebra.FiniteType R (B i) ∧ Module.Flat R (B i) ∧ IsOpenImmersion (u i) ∧
        u i ≫ f = spMap (algebraMap K _)) ∧
      ∀ (V L : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra R V] [Field L] [Algebra V L]
        [IsFractionRing V L] (a : Sp L ⟶ X),
        a ≫ f ≫ spMap (algebraMap R K) = spMap ((algebraMap V L).comp (algebraMap R V)) →
        ∃ (i : Fin m) (b : B i →ₐ[R] V) (ψ : TensorProduct R K (B i) →+* L), spMap ψ ≫ u i = a ∧
          ∀ x, ψ (1 ⊗ₜ x) = algebraMap V L (b x) := by sorry
