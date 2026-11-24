-- Prove2me | Theorems.Thm_GlobalTheory_unifPull_rig_compat
-- name    : GlobalTheory.unifPull_rig_compat
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:25:00.067241+00:00
-- url     : https://prove2.me/theorems/3ed4a102-99ed-4c37-a5b0-42c2f3cdf21d
-- title:
--   Global Theory: unif Pull rig compat
-- statement:
--   The Global Theory construction uses the unif Pull rig compat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CompatAlongOfSquare.lean#L186-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CompatAlongOfSquare.lean#L186-L223

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CompatAlongOfSquare
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
noncomputable section
open GlobalTheory
open UnifPullRig ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.unifPull_rig_compat : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), I.map φ ≤ I' → IsMonHom bc.hom → ∀ (U : UnifPre I D A G) (L' : RigLB G') (wL : LB.Iso L'.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf φ)))) (he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = specOf φ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig (rigPullOf (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (specOf φ) he U.LG.L U.LG.rig) → ∀ (gt' : ∀ e : ℕ, GtCoord I' D'.toPre e G') (w' : ∀ e : ℕ, LB.Iso (L'.L.pull (fstG I' e G').left) (D'.toPre.P.L.pull (gt' e).pG.left)), (∀ e, (w' e).IsGen) → (∀ e, thickMap R' I' e G' ≫ (gt' (e + 1)).pG.left = (gt' e).pG.left) → (∀ e : ℕ, ∃ (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I' e G').left ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ∧ ((gt' e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (gt' e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ Geo.Tor.PMaps hD.w (D'.toPre.Oφ (gt' e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((gt' e).t x) ((U.gt e).t (hD.xe x)) h) ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R' I' e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : L'.L.ι), ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((gt' e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (gt' e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → ((bc.hom.left ≫ pullback.fst G.hom (specOf φ))) ((fstG I' e G').left (r z)) ∈ U.LG.L.U jL → (fstG I' e G').left (r z) ∈ L'.L.U jL' → Geo.Tor.gw hD.w (r ≫ (gt' e).pG.left) z jM jM' * Geo.Tor.gw (w' e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I' e G').left) z jL jL')) → (∀ (e : ℕ) (p : (PUnit → D'.toPre.P.L.ι) × (PUnit → L'.L.ι)) (V : (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))).Opens) (h₁ : V ≤ eSec (thickObj R' I' e G') ⁻¹ᵁ ((D'.toPre.P.L.pull (gt' e).pG.left).U p.1 ⊓ (L'.L.pull (fstG I' e G').left).U p.2)) (h₂ : V ≤ thick R' I' e ⁻¹ᵁ (L'.L.pull (eSec G')).U p.2) (h₃ : V ≤ thick R' I' e ⁻¹ᵁ (D'.toPre.P.L.pull (eSec D'.toPre.P.A)).U p.1), res h₁ (pullU (eSec (thickObj R' I' e G')) _ ((w' e).s p)) * res h₂ (pullU (thick R' I' e) _ (L'.rig.s p.2)) = res h₃ (pullU (thick R' I' e) _ (D'.toPre.rig.s p.1))) ∧ (∀ (e : ℕ) (p : (PUnit → D'.toPre.P.L.ι) × (PUnit → L'.L.ι)) (V : (thickObj R' I' e G').left.Opens) (h₁ : V ≤ thickMap R' I' e G' ⁻¹ᵁ ((D'.toPre.P.L.pull (gt' (e + 1)).pG.left).U p.1 ⊓ (L'.L.pull (fstG I' (e + 1) G').left).U p.2)) (h₂ : V ≤ (D'.toPre.P.L.pull (gt' e).pG.left).U p.1 ⊓ (L'.L.pull (fstG I' e G').left).U p.2), res h₁ (pullU (thickMap R' I' e G') _ ((w' (e + 1)).s p)) = res h₂ ((w' e).s p)) := by sorry
