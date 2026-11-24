-- Prove2me | Theorems.Thm_GlobalTheory_pulled_comparison_even
-- name    : GlobalTheory.pulled_comparison_even
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:22:36.489276+00:00
-- url     : https://prove2.me/theorems/d318962b-400a-4385-9984-53fce2f6ae4d
-- title:
--   Global Theory: pulled comparison even
-- statement:
--   The Global Theory construction uses the pulled comparison even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PulledComparisonEven.lean#L203-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PulledComparisonEven.lean#L203-L225

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PulledComparisonEven
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.EvenPull

theorem GlobalTheory.pulled_comparison_even : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), I.map φ ≤ I' → IsMonHom bc.hom → ∀ (U : UnifPre I D A G) (L' : RigLB G') (wL : LB.Iso L'.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf φ)))) (he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = specOf φ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig (rigPullOf (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (specOf φ) he U.LG.L U.LG.rig) → ∀ (gt' : ∀ e : ℕ, GtCoord I' D'.toPre e G') (w' : ∀ e : ℕ, LB.Iso (L'.L.pull (fstG I' e G').left) (D'.toPre.P.L.pull (gt' e).pG.left)), (∀ e, (w' e).IsGen) → (∀ e, thickMap R' I' e G' ≫ (gt' (e + 1)).pG.left = (gt' e).pG.left) → (∀ e : ℕ, ∃ (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I' e G').left ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ∧ ((gt' e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (gt' e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ Geo.Tor.PMaps hD.w (D'.toPre.Oφ (gt' e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((gt' e).t x) ((U.gt e).t (hD.xe x)) h) ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R' I' e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : L'.L.ι), ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((gt' e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (gt' e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → ((bc.hom.left ≫ pullback.fst G.hom (specOf φ))) ((fstG I' e G').left (r z)) ∈ U.LG.L.U jL → (fstG I' e G').left (r z) ∈ L'.L.U jL' → Geo.Tor.gw hD.w (r ≫ (gt' e).pG.left) z jM jM' * Geo.Tor.gw (w' e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I' e G').left) z jL jL')) → ∀ (s' : LB.Gen (LB.LinComb L'.L (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![1, -1])), s'.IsGen → Geo.Tor.PMaps wL (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![(ι[G]).left, 𝟙 G.left] ![1, -1] s' U.symG (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) → ∀ (e : ℕ) (jS : Fin 2 → L'.L.ι) (jT : Fin 2 → D'.toPre.P.L.ι), LB.Coh L'.L (fun k => (fstG I' e G').left ≫ (![(ι[G']).left, 𝟙 G'.left] : Fin 2 → _) k) jS → LB.Coh D'.toPre.P.L (fun k => (gt' e).pG.left ≫ (![(ι[D'.toPre.P.A]).left, 𝟙 D'.toPre.P.A.left] : Fin 2 → _) k) jT → ∀ (V : (thickObj R' I' e G').left.Opens) (h₁ : V ≤ (gt' e).pG.left ⁻¹ᵁ (LB.LinComb D'.toPre.P.L (K := Fin 2) ![(ι[D'.toPre.P.A]).left, 𝟙 D'.toPre.P.A.left] ![1, -1]).U jT) (h₂ : V ≤ (D'.toPre.P.L.pull (gt' e).pG.left).U (fun _ => jT 1) ⊓ (L'.L.pull (fstG I' e G').left).U (fun _ => jS 1)) (h₃ : V ≤ (ι[thickObj R' I' e G']).left ⁻¹ᵁ ((D'.toPre.P.L.pull (gt' e).pG.left).U (fun _ => jT 0) ⊓ (L'.L.pull (fstG I' e G').left).U (fun _ => jS 0))) (h₄ : V ≤ (fstG I' e G').left ⁻¹ᵁ (LB.LinComb L'.L (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![1, -1]).U jS), res h₁ (pullU (gt' e).pG.left _ (D'.toPre.sym.s jT)) * res h₂ ((w' e).s (fun _ => jT 1, fun _ => jS 1)) = res h₃ (pullU (ι[thickObj R' I' e G']).left _ ((w' e).s (fun _ => jT 0, fun _ => jS 0))) * res h₄ (pullU (fstG I' e G').left _ (s'.s jS)) := by sorry
