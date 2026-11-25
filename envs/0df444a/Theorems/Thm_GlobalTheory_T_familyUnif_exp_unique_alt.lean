-- Prove2me | Theorems.Thm_GlobalTheory_T_familyUnif_exp_unique_alt
-- name    : GlobalTheory.T.familyUnif_exp_unique_alt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:23:00.558192+00:00
-- url     : https://prove2.me/theorems/e850531e-a89e-49a5-8f21-88cfe85982c3
-- title:
--   T: family Unif exp unique alt
-- statement:
--   The T construction uses the family Unif exp unique alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FamilyUnifExpUniqueStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FamilyUnifExpUniqueStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FamilyUnifExpUnique
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FamilyUnifExpUniqueStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.T.familyUnif_exp_unique_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i j : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ)) (P' : (U.Di j).La →+ (Fin g → ℂ)), IsPeriod (U.Di i) ty P → IsPeriod (U.Di j) ty P' → U.u i P = U.u j P' → ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (gam : (U.Di i).La ≃ₗ[𝓞 E] (U.Di j).La), (∀ z, (U.ex j P' (h z)).left = (U.ex i P z).left) ∧ (∀ a, P' (gam a) = h (P a)) ∧ (∀ a a', (U.Di j).EF (gam a) (gam a') = (U.Di i).EF a a') ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, gam (U.t i a) = U.t j a + l.M • e) ∧ ∀ a, ∃ e, gam (U.t i a) = U.t j a + l.A • e := by sorry
