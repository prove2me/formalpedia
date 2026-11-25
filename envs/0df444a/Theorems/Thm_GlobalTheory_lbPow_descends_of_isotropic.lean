-- Prove2me | Theorems.Thm_GlobalTheory_lbPow_descends_of_isotropic
-- name    : GlobalTheory.lbPow_descends_of_isotropic
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:52:13.487447+00:00
-- url     : https://prove2.me/theorems/7d492074-5c19-4e08-8aec-c6ef04ac07e3
-- title:
--   Global Theory: lb Pow descends of isotropic
-- statement:
--   The Global Theory construction uses the lb Pow descends of isotropic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LbPowDescendsOfIsotropic.lean#L277-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LbPowDescendsOfIsotropic.lean#L277-L299

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LbPowDescendsOfIsotropic
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
open ThetaSplit

theorem GlobalTheory.lbPow_descends_of_isotropic : Out.Laws → (∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (ψ : A ⟶ B) (C : Type) [CommGroup C] [Finite C] (i : C →* (𝟙_ (Over S) ⟶ A)) (L : LB A.left), L.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), (∀ x : Over.mk t ⟶ A, x ≫ ψ = 1 ↔ ∃ c, x = toUnit _ ≫ i c) ∧ ∀ c, toUnit (Over.mk t) ≫ i c = 1 → c = 1) → ∀ (u : ∀ c, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, ((toUnit A ≫ i c) * 𝟙 A).left] ![1, -1])), (∀ c, (u c).IsGen) → (∀ c c', LB.Gen.Corr L _ _ _ _ (u (c * c')) (LB.mulGen L _ _ _ _ (u c) (LB.pullGen L _ _ (u c') ((toUnit A ≫ i c) * 𝟙 A).left))) → ∃ M : LB B.left, M.IsLB ∧ LBIso L (M.pull ψ.left)) → ∀ (k : Type) [Field k] [IsAlgClosed k] (P : Out.PolAV (Sp k)) (n : ℕ) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ P.A)) (B : Over (Sp k)) [GrpObj B] (ψ : P.A ⟶ B), 0 < n → (n : k) ≠ 0 → (∀ x ∈ C, x ^ n = 1) → (∀ x ∈ C, ∀ y ∈ C, Out.WeilIs P.A P.L n x y 1) → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ x : 𝟙_ (Over (Sp k)) ⟶ P.A, x ≫ ψ = 1 ↔ x ∈ C) → ∃ M : LB B.left, M.IsLB ∧ LBIso (lbPow P.L n) (M.pull ψ.left) := by sorry
