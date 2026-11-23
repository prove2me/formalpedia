-- Prove2me | Theorems.Thm_GlobalTheory_PowLie_isLieComb_iff_prod
-- name    : GlobalTheory.PowLie.isLieComb_iff_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:07:10.681812+00:00
-- url     : https://prove2.me/theorems/8a1f81fb-e336-4276-8ac2-1a997948d516
-- title:
--   Pow Lie: is Lie Comb iff prod
-- statement:
--   The Pow Lie construction uses the is Lie Comb iff prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsLieCombIffProd.lean#L47-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsLieCombIffProd.lean#L47-L61

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieCombIffProd
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
noncomputable section
open GlobalTheory GlobalTheory.PowLie
variable {R : Type} [CommRing R]
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]

theorem GlobalTheory.PowLie.isLieComb_iff_prod {G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)} [GrpObj G] [IsCommMonObj G]
    {n : ℕ} (c : Fin n → R) (v : Fin n → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G)) (w : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR R ⟶ G) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieComb c v w ↔ w = ∏ i, _root_.GlobalTheory.PowLie.sc (c i) ≫ v i := by sorry
