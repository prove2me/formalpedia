-- Prove2me | Theorems.Thm_GlobalTheory_TorusUnit_IsMulLeft_value_mul
-- name    : GlobalTheory.TorusUnit.IsMulLeft.value_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:11:38.048802+00:00
-- url     : https://prove2.me/theorems/958e047e-3329-461d-bd86-80756963bdb1
-- title:
--   Is Mul Left: value mul
-- statement:
--   The Is Mul Left construction uses the value mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsUniqueCharacterOfMul.lean#L230-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsUniqueCharacterOfMul.lean#L230-L238

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_ringHom_ext_ZU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_ringHom_uliftInt_ext

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
open scoped CategoryTheory.Obj TensorProduct AlgebraMonoidAlgebra
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.TorusUnit
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (torusFst ringHom_ext_ZU ringHom_uliftInt_ext)
open AddMonoidAlgebra (single)
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]
variable {Y : Over S}

theorem GlobalTheory.TorusUnit.IsMulLeft.value_mul {ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)} (hρ : IsMulLeft ρ)
    {R : CommRingCat.{0}} (φ φ' ψ : torusRing ZU X ⟶ R) (y : Spec R ⟶ Y.left)
    (h : ∀ x : X, ψ.hom (single x 1) = φ.hom (single x 1) * φ'.hom (single x 1)) :
    (value ψ y).hom ρ = (value φ y).hom ρ * (value φ' y).hom ρ := by sorry
