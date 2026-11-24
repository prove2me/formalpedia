-- Prove2me | Theorems.Thm_GlobalTheory_gtCoord_compat_of_pull
-- name    : GlobalTheory.gtCoord_compat_of_pull
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:48.533388+00:00
-- url     : https://prove2.me/theorems/68d0a446-6d50-4a9c-a164-c568be612f53
-- title:
--   Global Theory: gt Coord compat of pull
-- statement:
--   The Global Theory construction uses the gt Coord compat of pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/GtCoordCompatOfPull.lean#L75-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/GtCoordCompatOfPull.lean#L75-L94

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_GtCoordCompatOfPull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open LevelCompat

theorem GlobalTheory.gtCoord_compat_of_pull : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R') (D : DegPre R) (D' : DegPre R') (hD : IsPullDeg φ D D') (I : Ideal R) (I' : Ideal R') (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (Ψ : G'.left ⟶ G.left) (e : ℕ) (g₀ : GtCoord I D e G) (g₁ : GtCoord I D (e + 1) G) (g₀' : GtCoord I' D' e G') (g₁' : GtCoord I' D' (e + 1) G') (h₀ : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left) (h₁ : (thickObj R' I' (e + 1) G').left ⟶ (thickObj R I (e + 1) G).left), h₀ ≫ (fstG I e G).left = (fstG I' e G').left ≫ Ψ → h₁ ≫ (fstG I (e + 1) G).left = (fstG I' (e + 1) G').left ≫ Ψ → ((g₀').pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h₀ ≫ (g₀).pG.left ∧ ∀ x : D'.X, (∀ κ : Fin 4, D'.Oφ (g₀').pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h₀ ≫ D.Oφ (g₀).pG (hD.xe x) κ) ∧ Geo.Tor.PMaps hD.w (D'.Oφ (g₀').pG x) (D.Oφ (g₀).pG (hD.xe x)) Oinvε ((g₀').t x) ((g₀).t (hD.xe x)) h₀) → ((g₁').pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h₁ ≫ (g₁).pG.left ∧ ∀ x : D'.X, (∀ κ : Fin 4, D'.Oφ (g₁').pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h₁ ≫ D.Oφ (g₁).pG (hD.xe x) κ) ∧ Geo.Tor.PMaps hD.w (D'.Oφ (g₁').pG x) (D.Oφ (g₁).pG (hD.xe x)) Oinvε ((g₁').t x) ((g₁).t (hD.xe x)) h₁) → thickMap R I e G ≫ g₁.pG.left = g₀.pG.left → (∀ χ : D.X, LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g₁.t χ) (thickMap R I e G)) (g₀.t χ)) → thickMap R' I' e G' ≫ g₁'.pG.left = g₀'.pG.left ∧ ∀ χ : D'.X, LB.Gen.Corr D'.P.L _ _ _ _ (LB.pullGen D'.P.L _ _ (g₁'.t χ) (thickMap R' I' e G')) (g₀'.t χ) := by sorry
