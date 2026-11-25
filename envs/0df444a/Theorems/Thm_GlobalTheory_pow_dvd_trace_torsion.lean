-- Prove2me | Theorems.Thm_GlobalTheory_pow_dvd_trace_torsion
-- name    : GlobalTheory.pow_dvd_trace_torsion
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T18:02:43.392472+00:00
-- url     : https://prove2.me/theorems/6860341d-7ff2-56f6-8af6-62a6c70885a9
-- title:
--   Global Theory: pow dvd trace torsion
-- statement:
--   The Global Theory construction uses the pow dvd trace torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsAlgHomLocalizationAugmentation.lean#L35-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsAlgHomLocalizationAugmentation.lean#L35-L51

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdTraceOfBalancedTensorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueTorsionPointFrobeniusLocalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionLocalPresentationSmoothGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIntegralOfLocalPresentationPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAlgHomLocalizationAugmentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory

theorem GlobalTheory.pow_dvd_trace_torsion :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (G : Over (Sp O)) [GrpObj G] [IsCommMonObj G] (n : ℕ) (H : Type) [CommRing H] [Algebra O H] [Module.Finite O H] [Module.Free O H] (y : specO O H ⟶ G) (g : ℕ), SmoothOfRelativeDimension g G.hom → y ^ n = 1 → (∀ (S : Type) [CommRing S] [Algebra O S] (z : specO O S ⟶ G), z ^ n = 1 → ∃! φ : H →ₐ[O] S, ptMap φ ≫ y = z) → ∀ h : H, (n : O) ^ g ∣ Algebra.trace O H h := by sorry
