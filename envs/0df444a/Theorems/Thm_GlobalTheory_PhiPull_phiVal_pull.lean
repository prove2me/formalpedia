-- Prove2me | Theorems.Thm_GlobalTheory_PhiPull_phiVal_pull
-- name    : GlobalTheory.PhiPull.phiVal_pull
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:57:11.856564+00:00
-- url     : https://prove2.me/theorems/316840f3-be44-48ea-b4bf-8049249467f9
-- title:
--   Phi Pull: phi Val pull
-- statement:
--   The Phi Pull construction uses the phi Val pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PhiRelTransport.lean#L182-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PhiRelTransport.lean#L182-L261

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiRelTransport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm

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
open GlobalTheory.PhiPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}
variable {F : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F]
variable (hD : IsPullDeg φ D D') (hT : (TF (R := R') F).hom ≫ spMap φ = (TF (R := R) F).hom)
  {Θ : (DegPre.BF D' F).left ⟶ (DegPre.BF D F).left}
  (hΘ₁ : Θ ≫ (fst (TF (R := R) F) D.P.A).left = (fst (TF (R := R') F) D'.P.A).left)
  (hΘ₂ : Θ ≫ (DegPre.prB D F).left = (DegPre.prB D' F).left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
  {T' : Over (Spec (CommRingCat.of R'))}
set_option maxHeartbeats 1000000
include hT hΘ₁ hΘ₂

theorem GlobalTheory.PhiPull.phiVal_pull (hG : GlobalFnsSt) {k : ℕ} (p₀ : QkPt D F k) (p₀' : QkPt D' F k) (hy : p₀'.y = hD.xe.symm p₀.y)
    (hg : IsPullGtF φ hD F p₀.g p₀'.g)
    (ν : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p₀.g.b) (DegPre.lineε k)))
    (ν' : LB.Gen (LB.LinComb D'.P.L (DegPre.lineφ D' F p₀'.g.b) (DegPre.lineε k)))
    (hl : ∀ i, DegPre.lineφ D' F p₀'.g.b i ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = 𝟙 _ ≫ DegPre.lineφ D F p₀.g.b i)
    (hν : PMaps hD.w (DegPre.lineφ D' F p₀'.g.b) (DegPre.lineφ D F p₀.g.b) (DegPre.lineε k) ν' ν (𝟙 _))
    (s s₂ : Fam D F k) (s' s₂' : Fam D' F k)
    (H₁ : (∀ x : D'.X, ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D' F).left) (z : Z) (p : Fin 4 → D.P.L.ι)
      (q : Fin 4 → D'.P.L.ι), (∀ κ, (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ((DegPre.famφ D' F x) κ (r z)) ∈ D.P.L.U (p κ)) →
      (∀ κ, (DegPre.famφ D' F x) κ (r z) ∈ D'.P.L.U (q κ)) →
      gs (r ≫ Θ) z (LB.wchart D.P.L (DegPre.famφ D F (hD.xe x)) p) ((s.s (hD.xe x)).f p) =
        (∏ κ, gw hD.w (r ≫ (DegPre.famφ D' F x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val *
          gs r z (LB.wchart D'.P.L (DegPre.famφ D' F x) q) ((s'.s x).f q)))
    (H₂ : (∀ x : D'.X, ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D' F).left) (z : Z) (p : Fin 4 → D.P.L.ι)
      (q : Fin 4 → D'.P.L.ι), (∀ κ, (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ((DegPre.famφ D' F x) κ (r z)) ∈ D.P.L.U (p κ)) →
      (∀ κ, (DegPre.famφ D' F x) κ (r z) ∈ D'.P.L.U (q κ)) →
      gs (r ≫ Θ) z (LB.wchart D.P.L (DegPre.famφ D F (hD.xe x)) p) ((s₂.s (hD.xe x)).f p) =
        (∏ κ, gw hD.w (r ≫ (DegPre.famφ D' F x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val *
          gs r z (LB.wchart D'.P.L (DegPre.famφ D' F x) q) ((s₂'.s x).f q)))
    (H : PhiVal p₀ ν s.s s₂.s) : PhiVal p₀' ν' s'.s s₂'.s := by sorry
