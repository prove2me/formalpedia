-- Prove2me | Theorems.Thm_GlobalTheory_w_cub_pull
-- name    : GlobalTheory.w_cub_pull
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:26:01.746544+00:00
-- url     : https://prove2.me/theorems/5866f984-eac5-468c-ba7b-f4f28fac583b
-- title:
--   Global Theory: w cub pull
-- statement:
--   The Global Theory construction uses the w cub pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TripleProductPointCompProjection.lean#L92-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TripleProductPointCompProjection.lean#L92-L237

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TripleProductPointCompProjection
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor WCub
set_option maxHeartbeats 1600000

theorem GlobalTheory.w_cub_pull : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain
    R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegData R I) (D' : DegData R' I') (hD
    : IsPullDeg φ D.toPre D'.toPre) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A'
    : PolAV (Spec (CommRingCat.of (FractionRing R')))) (G : Over (Spec (CommRingCat.of R))) [GrpObj
    G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc
    : G' ≅ (Over.pullback (specOf φ)).obj G), I.map φ ≤ I' → IsMonHom bc.hom → ∀ (U
    : UnifPre I D A G) (L' : RigLB G') (wL : LB.Iso L'.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst
    G.hom (specOf φ)))) (he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf
    φ) = specOf φ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit)
    (fun _ => eSec G') (fun _ => 1)) L'.rig (rigPullOf (bc.hom.left ≫ pullback.fst G.hom (specOf φ))
    (specOf φ) he U.LG.L U.LG.rig) → ∀ (gt' : ∀ e : ℕ, GtCoord I' D'.toPre e G') (w'
    : ∀ e : ℕ, LB.Iso (L'.L.pull (fstG I' e G').left) (D'.toPre.P.L.pull (gt'
    e).pG.left)), (∀ e, (w' e).IsGen) → (∀ e, thickMap R' I' e G' ≫ (gt' (e + 1)).pG.left = (gt'
    e).pG.left) → (∀ e : ℕ, ∃ (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left), h ≫ (fstG
    I e G).left = (fstG I' e G').left ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ∧ ((gt'
    e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ (U.gt e).pG.left ∧
    ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (gt' e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst
    D.toPre.P.A.hom (specOf φ)) = h ≫ D.toPre.Oφ (U.gt e).pG (hD.xe
    x) κ) ∧ Geo.Tor.PMaps hD.w (D'.toPre.Oφ (gt' e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe
    x)) Oinvε ((gt' e).t x) ((U.gt e).t (hD.xe x)) h) ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R' I'
    e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL'
    : L'.L.ι), ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((gt' e).pG.left (r
    z)) ∈ D.toPre.P.L.U jM → (gt' e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → ((bc.hom.left ≫
    pullback.fst G.hom (specOf φ))) ((fstG I' e G').left (r z)) ∈ U.LG.L.U jL → (fstG I' e
    G').left (r z) ∈ L'.L.U jL' → Geo.Tor.gw hD.w (r ≫ (gt' e).pG.left) z jM jM' * Geo.Tor.gw (w'
    e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫
    (fstG I' e G').left) z jL jL')) → ∀ (hgp : Geo.Tor.IsGrpPullback G' G (specOf φ) (bc.hom.left ≫
    pullback.fst G.hom (specOf φ))) (c' : CubicalStr G' L'), Geo.Tor.PMaps wL (thφ G' (x3 G')) (thφ
    G (x3 G)) thε c'.t U.cubG.t (Geo.Tor.cubeMapOf hgp).F3 → ∀ (e : ℕ) (T : Over (Spec
    (CommRingCat.of (R' ⧸ I' ^ (e + 1))))) (x : Fin 3 → (T ⟶ thickObj R' I' e G')) (jL
    : thK → L'.L.ι) (jM : thK → D'.toPre.P.L.ι), LB.Coh L'.L (fun k => (lift ((Over.map (thick R' I'
    e)).map (x 0) ≫ fstG I' e G') (lift ((Over.map (thick R' I' e)).map (x 1) ≫ fstG I' e G')
    ((Over.map (thick R' I' e)).map (x 2) ≫ fstG I' e G'))).left ≫ thφ G' (x3
    G') k) jL → LB.Coh D'.toPre.P.L (fun k => (lift ((Over.map (thick R' I' e)).map (x 0) ≫ (gt'
    e).pG) (lift ((Over.map (thick R' I' e)).map (x 1) ≫ (gt' e).pG) ((Over.map (thick R' I' e)).map
    (x 2) ≫ (gt' e).pG))).left ≫ thφ D'.toPre.P.A (x3 D'.toPre.P.A) k) jM → ∀ (V : T.left.Opens) (hB
    : V ≤ (lift ((Over.map (thick R' I' e)).map (x 0) ≫ (gt' e).pG) (lift ((Over.map (thick R' I'
    e)).map (x 1) ≫ (gt' e).pG) ((Over.map (thick R' I' e)).map (x 2) ≫ (gt'
    e).pG))).left ⁻¹ᵁ (Theta D'.toPre.P.A D'.toPre.P.L).U jM) (hG : V ≤ (lift ((Over.map (thick R'
    I' e)).map (x 0) ≫ fstG I' e G') (lift ((Over.map (thick R' I' e)).map (x 1) ≫ fstG I' e G')
    ((Over.map (thick R' I' e)).map (x 2) ≫ fstG I' e G'))).left ⁻¹ᵁ (Theta G' L'.L).U jL) (hw
    : ∀ k : thK, V ≤ (psum (thickObj R' I' e G') x k.down).left ⁻¹ᵁ ((D'.toPre.P.L.pull (gt'
    e).pG.left).U (fun _ => jM k) ⊓ (L'.L.pull (fstG I' e G').left).U
    (fun _ => jL k))), res hB (pullU _ _ (D'.toPre.cub.t.s jM)) = (∏ k : thK, res (hw k) (pullU
    (psum (thickObj R' I' e G') x k.down).left _ ((w' e).s
    (fun _ => jM k, fun _ => jL k))) ^ thε k) * res hG (pullU _ _ (c'.t.s jL)) := by sorry
