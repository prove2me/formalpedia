-- Prove2me | Theorems.Thm_GlobalTheory_KS_Kunneth_pushout_functional
-- name    : GlobalTheory.KS.Kunneth.pushout_functional
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:45:56.614865+00:00
-- url     : https://prove2.me/theorems/8d330302-d90f-41bc-9343-3b05699d7e3f
-- title:
--   Kunneth: pushout functional
-- statement:
--   The Kunneth construction uses the pushout functional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/KunnethSymmProductAffineCovers.lean#L16-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/KunnethSymmProductAffineCovers.lean#L16-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDualFamilyModSubspace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KunnethSymmProductAffineCovers
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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Kunneth

theorem GlobalTheory.KS.Kunneth.pushout_functional {K : Type} [Field K] {A B C : CommRingCat.{0}} (f : CommRingCat.of K ⟶ A)
    (g : CommRingCat.of K ⟶ B) (i : A ⟶ C) (j : B ⟶ C) (po : IsPushout f g i j) :
    (∀ (α : A →+ K) (β : B →+ K), (∀ c a, α (f.hom c * a) = c * α a) → (∀ c b, β (g.hom c * b) = c * β b) →
      ∃ F : C →+ K, ∀ a b, F (i.hom a * j.hom b) = α a * β b) ∧
    ∀ G : C →+ K, (∀ a b, G (i.hom a * j.hom b) = 0) → ∀ w, G w = 0 := by sorry
