-- Prove2me | Theorems.Thm_GlobalTheory_exists_sabMap_of_isProper_of_lbIso
-- name    : GlobalTheory.exists_sabMap_of_isProper_of_lbIso
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:19:20.143811+00:00
-- url     : https://prove2.me/theorems/8e1f3481-1051-4acd-ac6f-c53400b363af
-- title:
--   Global Theory: exists sab Map of is Proper of lb Iso
-- statement:
--   The Global Theory construction uses the exists sab Map of is Proper of lb Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqOneOfSurjectiveAppTopOfSection.lean#L25-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqOneOfSurjectiveAppTopOfSection.lean#L25-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSabMapOfLbIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOneOfSurjectiveAppTopOfSection
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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory

theorem GlobalTheory.exists_sabMap_of_isProper_of_lbIso : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (φ : t'.G.left ⟶ t.G.left), IsProper t.G.hom → IsGrpPullback t'.G t.G f φ → LBIso t'.PP.L (t.PP.L.pull φ) → (∀ a, (t'.act.act a).left ≫ φ = φ ≫ (t.act.act a).left) → ∃ m : SABMap t' t f, m.φ = φ := by sorry
