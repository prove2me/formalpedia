-- Prove2me | Theorems.Thm_GlobalTheory_DetExtend_lieMult_iff_finrank
-- name    : GlobalTheory.DetExtend.lieMult_iff_finrank
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:41:06.672191+00:00
-- url     : https://prove2.me/theorems/a89efe9f-7234-5c82-8d0c-0ae379ca5d5f
-- title:
--   Det Extend: lie Mult iff finrank
-- statement:
--   The Det Extend construction uses the lie Mult iff finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DetCondIffOfFieldExtension.lean#L33-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DetCondIffOfFieldExtension.lean#L33-L89

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPushEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetCondIffOfFieldExtension
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
open GlobalTheory GlobalTheory.DetExtend
open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD tvec tmap eigLat IsUnivChart)

theorem GlobalTheory.DetExtend.lieMult_iff_finrank {k : Type} [Field k] {O : Type} [CommRing O] {G : Over (Sp k)} [GrpObj G]
    (act : OAct O G) [∀ a, IsMonHom (act.act a)] {n : ℕ}
    {x : ∀ m : ℕ, Chart.sp (R₀ := k) (Chart.JetR k (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)
    (τ : O →+* k) (N : ℕ) :
    LieMult act (𝟙 (Sp k)) τ N ↔ Module.finrank k (eigLat hx act.act (fun a => τ a)) = N := by sorry
