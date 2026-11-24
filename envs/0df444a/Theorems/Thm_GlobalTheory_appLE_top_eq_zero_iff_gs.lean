-- Prove2me | Theorems.Thm_GlobalTheory_appLE_top_eq_zero_iff_gs
-- name    : GlobalTheory.appLE_top_eq_zero_iff_gs
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:06:11.734793+00:00
-- url     : https://prove2.me/theorems/df5da5e1-54c8-49fc-a743-c4c5c3fa7a19
-- title:
--   Global Theory: app LE top eq zero iff gs
-- statement:
--   The Global Theory construction uses the app LE top eq zero iff gs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/KernelPolarisationTrivialOfSectionsVanishZero.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/KernelPolarisationTrivialOfSectionsVanishZero.lean#L14-L20

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsGenTranslDiffComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_KernelPolarisationTrivialOfSectionsVanishZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

theorem GlobalTheory.appLE_top_eq_zero_iff_gs {X Z : Scheme.{0}} (r : Z ⟶ X) (U : X.Opens) (h : ⊤ ≤ r ⁻¹ᵁ U) (a : Γ(X, U)) :
    (r.appLE U ⊤ h).hom a = 0 ↔ ∀ z, gs r z U a = 0 := by sorry
