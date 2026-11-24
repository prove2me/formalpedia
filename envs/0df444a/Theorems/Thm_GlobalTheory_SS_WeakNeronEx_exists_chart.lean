-- Prove2me | Theorems.Thm_GlobalTheory_SS_WeakNeronEx_exists_chart
-- name    : GlobalTheory.SS.WeakNeronEx.exists_chart
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:11:46.54489+00:00
-- url     : https://prove2.me/theorems/6f4be3db-79d4-4b5d-93b9-33e77636aadb
-- title:
--   Weak Neron Ex: exists chart
-- statement:
--   The Weak Neron Ex construction uses the exists chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsWeakNeronModel.lean#L96-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsWeakNeronModel.lean#L96-L125

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart

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

theorem GlobalTheory.SS.WeakNeronEx.exists_chart {X : Scheme.{0}} {H : LB X} {m : ℕ} (s : Fin (m + 1) → LB.Sec H)
    (hc : ⨆ i, nonzeroLocus (s i) = ⊤) (r : ∀ i, Fin (m + 1) → Γ(X, nonzeroLocus (s i)))
    (hr : ∀ i j k, rs X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s j).f k) =
        rs X (inf_le_left : nonzeroLocus (s i) ⊓ H.U k ≤ nonzeroLocus (s i)) (r i j) *
          rs X (inf_le_right : nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s i).f k))
    {V L : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field L] [Algebra V L]
    [IsFractionRing V L] (a : Sp L ⟶ X) :
    ∃ (i : Fin (m + 1)) (h : ⊤ ≤ a ⁻¹ᵁ nonzeroLocus (s i)), ∀ j, ev a _ h (r i j) ∈ (algebraMap V L).range := by sorry
