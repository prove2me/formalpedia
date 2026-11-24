-- Prove2me | Theorems.Thm_GlobalTheory_RigidLinearisation_exists_linearisation
-- name    : GlobalTheory.RigidLinearisation.exists_linearisation
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:24:59.204232+00:00
-- url     : https://prove2.me/theorems/4ba4c0c9-fedb-4227-a6cf-2c95aed61297
-- title:
--   Rigid Linearisation: exists linearisation
-- statement:
--   The Rigid Linearisation construction uses the exists linearisation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLinearisation.lean#L112-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLinearisation.lean#L112-L174

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLinearisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.RigidLinearisation

theorem GlobalTheory.RigidLinearisation.exists_linearisation : ∀ (Γ : Type) [Group Γ] [Finite Γ] (X : Scheme.{0}) (P : Over X) (e : X ⟶ P.left) (ρ : Γ →* Aut X) (τ : Γ →* Aut P.left) (L : LB P.left), e ≫ P.hom = 𝟙 X → GeometricallyIntegral P.hom → (∀ (V : X.Opens) (u : Γ(P.left, P.hom ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (P.hom ⁻¹ᵁ V)), (e.appLE _ V h).hom u = 1 → u = 1) → (∀ g, (τ g).hom ≫ P.hom = P.hom ≫ (ρ g).hom ∧ e ≫ (τ g).hom = (ρ g).hom ≫ e) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) g, x ≫ (ρ g).hom = x → pullback.fst P.hom x ≫ (τ g).hom = pullback.fst P.hom x) → L.IsLB → (∃ r : (L.pull e).Gen, r.IsGen) → (∀ g, LBIso L (L.pull (τ g).hom)) → ∃ u : ∀ g, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 P.left, (τ g).hom] ![1, -1]), (∀ g, (u g).IsGen) ∧ (∀ g h, LB.Gen.Corr L _ _ _ _ (u (h * g)) (LB.mulGen L _ _ _ _ (u g) (LB.pullGen L _ _ (u h) (τ g).hom))) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ P.left) g, y ≫ (τ g).hom = y → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ (u g) y) (LB.oneGen L) := by sorry
