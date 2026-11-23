-- Prove2me | Theorems.Thm_GlobalTheory_expandsAt_transport
-- name    : GlobalTheory.expandsAt_transport
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:23:53.057477+00:00
-- url     : https://prove2.me/theorems/2b414059-bdf3-4784-9172-d5a92d78bd4b
-- title:
--   Global Theory: expands At transport
-- statement:
--   The Global Theory construction uses the expands At transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExpandsAtTransport.lean#L77-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExpandsAtTransport.lean#L77-L118

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ExpTrans
set_option maxHeartbeats 1600000

theorem GlobalTheory.expandsAt_transport : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (D : DegData R I) (D' : DegData R' I') (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (U : UnifPre I D A G) (U' : UnifPre I' D' A' G') (Φ : D'.toPre.P.A.left ⟶ D.toPre.P.A.left) (w : LB.Iso D'.toPre.P.L (D.toPre.P.L.pull Φ)) (xe : D'.toPre.X ≃+ D.toPre.X) (Ψ : G'.left ⟶ G.left) (wL : LB.Iso U'.LG.L (U.LG.L.pull Ψ)), w.IsGen → wL.IsGen → (∀ x κ, D'.toPre.famφB x κ ≫ Φ = Φ ≫ D.toPre.famφB (xe x) κ) → ∀ (e e' k : ℕ) (h : (thickObj R' I' e' G').left ⟶ (thickObj R I e G).left), (h ≫ (fstG I e G).left = (fstG I' e' G').left ≫ Ψ ∧ ((U'.gt e').pG.left ≫ Φ = h ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e').pG x κ ≫ Φ = h ≫ D.toPre.Oφ (U.gt e).pG (xe x) κ) ∧ Geo.Tor.PMaps w (D'.toPre.Oφ (U'.gt e').pG x) (D.toPre.Oφ (U.gt e).pG (xe x)) Oinvε ((U'.gt e').t x) ((U.gt e).t (xe x)) h) ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R' I' e' G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (Φ) ((U'.gt e').pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e').pG.left (r z) ∈ D'.toPre.P.L.U jM' → (Ψ) ((fstG I' e' G').left (r z)) ∈ U.LG.L.U jL → (fstG I' e' G').left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw w (r ≫ (U'.gt e').pG.left) z jM jM' * Geo.Tor.gw (U'.w e') r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I' e' G').left) z jL jL')) → ∀ (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) (σ' : LB.Sec (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G'.left) (fun _ => (k : ℤ)))) (f : ∀ α, D.toPre.SecB k α) (f' : ∀ α, D'.toPre.SecB k α), (∀ (Z : Scheme.{0}) (r : Z ⟶ G'.left) (z : Z) (p : Fin 1 → U.LG.L.ι) (q : Fin 1 → U'.LG.L.ι), (∀ κ, (Ψ) ((fun _ : Fin 1 => 𝟙 G'.left) κ (r z)) ∈ U.LG.L.U (p κ)) → (∀ κ, (fun _ : Fin 1 => 𝟙 G'.left) κ (r z) ∈ U'.LG.L.U (q κ)) → Geo.Tor.gs (r ≫ Ψ) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) p) ((σ).f p) = (∏ κ, Geo.Tor.gw wL (r ≫ (fun _ : Fin 1 => 𝟙 G'.left) κ) z (p κ) (q κ) ^ (fun _ : Fin 1 => (k : ℤ)) κ).val * Geo.Tor.gs r z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) q) ((σ').f q)) → (∀ x : D'.toPre.X, (∀ (Z : Scheme.{0}) (r : Z ⟶ D'.toPre.P.A.left) (z : Z) (p : Fin 4 → D.toPre.P.L.ι) (q : Fin 4 → D'.toPre.P.L.ι), (∀ κ, (Φ) ((D'.toPre.famφB x) κ (r z)) ∈ D.toPre.P.L.U (p κ)) → (∀ κ, (D'.toPre.famφB x) κ (r z) ∈ D'.toPre.P.L.U (q κ)) → Geo.Tor.gs (r ≫ Φ) z (LB.wchart D.toPre.P.L (D.toPre.famφB (xe x)) p) ((f (xe x)).f p) = (∏ κ, Geo.Tor.gw w (r ≫ (D'.toPre.famφB x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.toPre.P.L (D'.toPre.famφB x) q) ((f' x).f q))) → U.ExpandsAt e k σ f → U'.ExpandsAt e' k σ' f' := by sorry
