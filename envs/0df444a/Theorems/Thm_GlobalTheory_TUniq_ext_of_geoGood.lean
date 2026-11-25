-- Prove2me | Theorems.Thm_GlobalTheory_TUniq_ext_of_geoGood
-- name    : GlobalTheory.TUniq.ext_of_geoGood
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:56:47.678316+00:00
-- url     : https://prove2.me/theorems/7ccaeb97-423d-5110-868d-8a9e7b095612
-- title:
--   TUniq: ext of geo Good
-- statement:
--   The TUniq construction uses the ext of geo Good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsCompatOfLocal.lean#L49-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsCompatOfLocal.lean#L49-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLiftClosedImmersionOfDense
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCompatOfLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.TUniq
variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {S S' : Scheme.{0}} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o}

theorem GlobalTheory.TUniq.ext_of_geoGood {t t' : TObj g k J b s} {Sg : Set S} (hd : Dense Sg) (hg : GeoGood t t' Sg) {X Y : Scheme.{0}}
    [IsReduced X] (p : X ⟶ S) [Flat p] [LocallyOfFinitePresentation p] (q : Y ⟶ S) [IsSeparated q] {f f' : X ⟶ Y}
    (hf : f ≫ q = p) (hf' : f' ≫ q = p)
    (H : ∀ (K : Type) [Field K] [IsAlgClosed K] (su : Sp K ⟶ Sp o) (u : TObj g k J b su) (x : Sp K ⟶ S)
      (ψ : u.A.left ⟶ t.A.left) (ψ' : u.A.left ⟶ t'.A.left), MapBy u t x ψ → MapBy u t' x ψ' →
      ∀ y : Sp K ⟶ X, y ≫ p = x → y ≫ f = y ≫ f') : f = f' := by sorry
