-- Prove2me | Theorems.Thm_GlobalTheory_phi_specialises
-- name    : GlobalTheory.phi_specialises
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:15:34.721791+00:00
-- url     : https://prove2.me/theorems/de280902-4fd7-4339-8ba1-52a0b0979bb4
-- title:
--   Global Theory: phi specialises
-- statement:
--   The Global Theory construction uses the phi specialises property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PhiSpecialises.lean#L435-L472
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PhiSpecialises.lean#L435-L472

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiRelTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PhiSpecialises
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

theorem GlobalTheory.phi_specialises : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre), ∀ (S : Type) [CommRing S] [IsDomain S] [ValuationRing S] (σ : R →+* S) (F : Type) [Field F] [Algebra (FractionRing R) F] (ιF : S →+* F), Function.Injective ιF → ∀ (ρ : TF (R := R) F ⟶ (Over.mk (specOf σ))), ρ.left = specOf ιF → ∀ (F' : Type) [Field F'] [Algebra (FractionRing R') F'] (π : S →+* F'), IsLocalHom π → (∀ r : R, π (σ r) = algebraMap (FractionRing R') F' (algebraMap R' (FractionRing R') (φ r))) → ∀ (Θ : (DegPre.BF D'.toPre F').left ⟶ ((Over.mk (specOf σ)) ⊗ D.toPre.P.A).left), Θ ≫ (fst (Over.mk (specOf σ)) D.toPre.P.A).left = (fst (TF (R := R') F') D'.toPre.P.A).left ≫ specOf π → Θ ≫ (snd (Over.mk (specOf σ)) D.toPre.P.A).left = (DegPre.prB D'.toPre F').left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) → ∀ (k : ℕ), 1 ≤ k → ∀ (gp : GtPt D.toPre (Over.mk (specOf σ))) (p₀ : QkPt D.toPre F k) (p₁ : QkPt D'.toPre F' k), GtPt.IsPullF F ρ.left gp p₀.g → p₁.y = hD.xe.symm p₀.y → p₁.g.b.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = specOf π ≫ gp.b.left → (∀ χ, Geo.Tor.PMaps hD.w (DegPre.gtφ D'.toPre F' p₁.g.b χ) (DegPre.gtφT D.toPre (Over.mk (specOf σ)) gp.b (hD.xe χ)) DegPre.gtε (p₁.g.s χ) (gp.s (hD.xe χ)) (specOf π)) → ∃ (ν : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p₀.g.b) (DegPre.lineε k))) (ν' : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F' p₁.g.b) (DegPre.lineε k))), ν.IsGen ∧ ν'.IsGen ∧ ∀ (s : Fam D.toPre F k) (s' : Fam D'.toPre F' k) (g : ∀ α, LB.Sec (LB.LinComb D.toPre.P.L (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k))), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α) (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k) (g α) (ρ ▷ D.toPre.P.A).left 1) → (∀ (x : D'.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D'.toPre F').left) (z : Z) (p : Fin 4 → D.toPre.P.L.ι) (q : Fin 4 → D'.toPre.P.L.ι), (∀ κ, (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) ((DegPre.famφ D'.toPre F' x) κ (r z)) ∈ D.toPre.P.L.U (p κ)) → (∀ κ, (DegPre.famφ D'.toPre F' x) κ (r z) ∈ D'.toPre.P.L.U (q κ)) → Geo.Tor.gs (r ≫ Θ) z (LB.wchart D.toPre.P.L (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB (hD.xe x) i) p) ((g (hD.xe x)).f p) = (∏ κ, Geo.Tor.gw hD.w (r ≫ (DegPre.famφ D'.toPre F' x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.toPre.P.L (DegPre.famφ D'.toPre F' x) q) ((s'.s x).f q)) → ∃ (s₂ : Fam D.toPre F k) (s₂' : Fam D'.toPre F' k) (g₂ : ∀ α, LB.Sec (LB.LinComb D.toPre.P.L (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k))), PhiRel D.toPre F k p₀ ν s s₂ ∧ PhiRel D'.toPre F' k p₁ ν' s' s₂' ∧ (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s₂.s α) (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB α i) (DegPre.famε k) (g₂ α) (ρ ▷ D.toPre.P.A).left 1) ∧ (∀ (x : D'.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D'.toPre F').left) (z : Z) (p : Fin 4 → D.toPre.P.L.ι) (q : Fin 4 → D'.toPre.P.L.ι), (∀ κ, (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) ((DegPre.famφ D'.toPre F' x) κ (r z)) ∈ D.toPre.P.L.U (p κ)) → (∀ κ, (DegPre.famφ D'.toPre F' x) κ (r z) ∈ D'.toPre.P.L.U (q κ)) → Geo.Tor.gs (r ≫ Θ) z (LB.wchart D.toPre.P.L (fun i => (snd (Over.mk (specOf σ)) D.toPre.P.A).left ≫ D.toPre.famφB (hD.xe x) i) p) ((g₂ (hD.xe x)).f p) = (∏ κ, Geo.Tor.gw hD.w (r ≫ (DegPre.famφ D'.toPre F' x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.toPre.P.L (DegPre.famφ D'.toPre F' x) q) ((s₂'.s x).f q)) := by sorry
