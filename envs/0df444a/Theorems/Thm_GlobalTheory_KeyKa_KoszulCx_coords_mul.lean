-- Prove2me | Theorems.Thm_GlobalTheory_KeyKa_KoszulCx_coords_mul
-- name    : GlobalTheory.KeyKa.KoszulCx.coords_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:44.466846+00:00
-- url     : https://prove2.me/theorems/9e7ff7b4-bc3e-42ed-876e-49db7c1f5e3f
-- title:
--   Koszul Cx: coords mul
-- statement:
--   The Koszul Cx construction uses the coords mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SignInsert.lean#L205-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SignInsert.lean#L205-L209

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SignInsert
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.KoszulCx
variable {R : Type} [CommRing R]

theorem GlobalTheory.KeyKa.KoszulCx.coords_mul (x : KeyIn R) {l₀ l₁ N₀ N₁ : ℕ} (b₀ : Fin N₀ → RR x l₀) (b₁ : Fin N₁ → RR x l₁)
    (M : Matrix (Fin N₀) (Fin N₁) R) (u f : ∀ i, Γ(x.P.A.left, x.P.L.U i)) (c : Fin N₁ → R)
    (hM : ∀ k, Coords x b₀ (fun k' => M k' k) (fun i => u i * (show Γ(x.P.A.left, x.P.L.U i) from (b₁ k).f i)))
    (hc : Coords x b₁ c f) : Coords x b₀ (fun k' => ∑ k, M k' k * c k) (fun i => u i * f i) := by sorry
