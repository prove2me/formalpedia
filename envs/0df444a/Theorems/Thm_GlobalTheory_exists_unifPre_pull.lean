-- Prove2me | Theorems.Thm_GlobalTheory_exists_unifPre_pull
-- name    : GlobalTheory.exists_unifPre_pull
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T15:11:02.257184+00:00
-- url     : https://prove2.me/theorems/75773ec4-55de-4b7f-992d-c2042eb4aa35
-- title:
--   Global Theory: exists unif Pre pull
-- statement:
--   The Global Theory construction uses the exists unif Pre pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsUnifPrePull.lean#L25-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsUnifPrePull.lean#L25-L54

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPullbackPullbackMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGrpPullbackThick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_GtCoordCompatOfPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubicalSymmetryTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFourthSide
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CompatAlongOfSquare
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PulledComparisonEven
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TripleProductPointCompProjection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnifPrePull
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.exists_unifPre_pull : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), I.map φ ≤ I' → IsMonHom bc.hom → ∀ (U : UnifPre I D A G) (eA : (Over.pullback (jK R')).obj G' ≅ A'.A), IsMonHom eA.hom → (∃ wA : LB.Iso (A'.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ))), wA.IsGen) → ∀ (L' : RigLB G') (wL : LB.Iso L'.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf φ)))) (he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = specOf φ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig (rigPullOf (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (specOf φ) he U.LG.L U.LG.rig) → ∃ (U' : UnifPre I' D' A' G') (wL' : LB.Iso U'.LG.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf φ)))), U'.LG = L' ∧ U'.gen = eA ∧ HEq wL' wL ∧ ∀ e : ℕ, ∃ (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I' e G').left ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ∧ ((U'.gt e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ Geo.Tor.PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (hD.xe x)) h) ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R' I' e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((U'.gt e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → ((bc.hom.left ≫ pullback.fst G.hom (specOf φ))) ((fstG I' e G').left (r z)) ∈ U.LG.L.U jL → (fstG I' e G').left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL' (r ≫ (fstG I' e G').left) z jL jL') := by sorry
