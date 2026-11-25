-- Prove2me | Theorems.Thm_GlobalTheory_expandsG_transport
-- name    : GlobalTheory.expandsG_transport
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:29:16.034281+00:00
-- url     : https://prove2.me/theorems/76dd9cef-7d7f-401d-9318-fbbc7992b81c
-- title:
--   Global Theory: expands G transport
-- statement:
--   The Global Theory construction uses the expands G transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExpandsGTransport.lean#L184-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExpandsGTransport.lean#L184-L262

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsGTransport
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ExpGTrans
set_option maxHeartbeats 1600000

theorem GlobalTheory.expandsG_transport : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain
    R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegData R I) (D' : DegData R' I') (hD
    : IsPullDeg φ D.toPre D'.toPre) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A'
    : PolAV (Spec (CommRingCat.of (FractionRing R')))) (G : Over (Spec (CommRingCat.of R))) [GrpObj
    G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc
    : G' ≅ (Over.pullback (specOf φ)).obj G), IsMonHom bc.hom → ∀ (U : UnifPre I D A G) (U'
    : UnifPre I' D' A' G') (wL : LB.Iso U'.LG.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom
    (specOf φ)))), wL.IsGen → (∀ e : ℕ, ∃ h : (thickObj R' I' e G').left ⟶ (thickObj R I e
    G).left, h ≫ (fstG I e G).left = (fstG I' e G').left ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf
    φ)) ∧ ((U'.gt e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ (U.gt
    e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ (hD.e.hom.left ≫
    pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ D.toPre.Oφ (U.gt e).pG (hD.xe
    x) κ) ∧ Geo.Tor.PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe
    x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (hD.xe x)) h) ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R'
    I' e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL'
    : U'.LG.L.ι), ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((U'.gt e).pG.left (r
    z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → ((bc.hom.left ≫
    pullback.fst G.hom (specOf φ))) ((fstG I' e G').left (r z)) ∈ U.LG.L.U jL → (fstG I' e
    G').left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw hD.w (r ≫ (U'.gt
    e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) (r ≫
    h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I' e G').left) z jL jL')) → ∀ (F : Type) [Field
    F] [Algebra (FractionRing R) F] [Algebra (FractionRing R')
    F], (∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R)
    r) = algebraMap (FractionRing R') F (algebraMap R' (FractionRing R') (φ r))) → ∀ (Θ : (DegPre.BF
    D'.toPre F).left ⟶ (DegPre.BF D.toPre F).left), Θ ≫ (fst (TF (R := R) F)
    D.toPre.P.A).left = (fst (TF (R := R') F) D'.toPre.P.A).left → Θ ≫ (DegPre.prB D.toPre
    F).left = (DegPre.prB D'.toPre F).left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf
    φ)) → ∀ (Ξ : (UnifPre.GF (G := G') F).left ⟶ (UnifPre.GF (G := G) F).left), Ξ ≫ (fst (TFK (R :=
    R) F) ((Over.pullback (jK R)).obj G)).left = (fst (TFK (R := R') F) ((Over.pullback (jK R')).obj
    G')).left → Ξ ≫ UnifPre.gFK (G := G) F = UnifPre.gFK (G := G') F ≫ (bc.hom.left ≫ pullback.fst
    G.hom (specOf φ)) → ∀ (k : ℕ) (σ : U.SecGF F k) (σ' : U'.SecGF F k) (s : Fam D.toPre F k) (s'
    : Fam D'.toPre F k), (∀ (Z : Scheme.{0}) (r : Z ⟶ (UnifPre.GF (G := G') F).left) (z : Z) (p
    : Fin 1 → U.LG.L.ι) (q : Fin 1 → U'.LG.L.ι), (∀ κ, ((bc.hom.left ≫ pullback.fst G.hom (specOf
    φ))) ((fun _ : Fin 1 => UnifPre.gFK (G := G') F) κ (r z)) ∈ U.LG.L.U (p
    κ)) → (∀ κ, (fun _ : Fin 1 => UnifPre.gFK (G := G') F) κ (r z) ∈ U'.LG.L.U (q
    κ)) → Geo.Tor.gs (r ≫ Ξ) z (LB.wchart U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) p) ((σ).f
    p) = (∏ κ, Geo.Tor.gw wL (r ≫ (fun _ : Fin 1 => UnifPre.gFK (G := G') F) κ) z (p κ) (q
    κ) ^ (fun _ : Fin 1 => (k : ℤ)) κ).val * Geo.Tor.gs r z (LB.wchart U'.LG.L
    (fun _ : Fin 1 => UnifPre.gFK (G := G') F) q) ((σ').f q)) → (∀ x : D'.toPre.X, (∀ (Z
    : Scheme.{0}) (r : Z ⟶ (DegPre.BF D'.toPre F).left) (z : Z) (p : Fin 4 → D.toPre.P.L.ι) (q
    : Fin 4 → D'.toPre.P.L.ι), (∀ κ, ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf
    φ))) ((DegPre.famφ D'.toPre F x) κ (r z)) ∈ D.toPre.P.L.U (p κ)) → (∀ κ, (DegPre.famφ D'.toPre F
    x) κ (r z) ∈ D'.toPre.P.L.U (q κ)) → Geo.Tor.gs (r ≫ Θ) z (LB.wchart D.toPre.P.L (DegPre.famφ
    D.toPre F (hD.xe x)) p) ((s.s (hD.xe x)).f p) = (∏ κ, Geo.Tor.gw hD.w (r ≫ (DegPre.famφ D'.toPre
    F x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.toPre.P.L
    (DegPre.famφ D'.toPre F x) q) ((s'.s x).f
    q))) → U.ExpandsG F k σ s → U'.ExpandsG F k σ' s' := by sorry
