-- Prove2me | Theorems.Thm_GlobalTheory_isReduced_torsion_geometric_fibre
-- name    : GlobalTheory.isReduced_torsion_geometric_fibre
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:02:20.3403+00:00
-- url     : https://prove2.me/theorems/66932d99-9322-4fa3-8d2e-ad391fe9fd7e
-- title:
--   Global Theory: is Reduced torsion geometric fibre
-- statement:
--   The Global Theory construction uses the is Reduced torsion geometric fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsReducedTorsionGeometricFibre.lean#L92-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsReducedTorsionGeometricFibre.lean#L92-L130

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowEqScaleAndExistsUniqueTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsReducedTorsionGeometricFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

theorem GlobalTheory.isReduced_torsion_geometric_fibre :
    ∀ (O F : Type) [CommRing O] [Field F] [IsAlgClosed F] [Algebra O F] (G : Over (Spec (CommRingCat.of O))) [GrpObj G] [IsCommMonObj G] (N : ℕ), (N : F) ≠ 0 → IsFinite (torsion G N).hom → IsReduced (specO O F ⊗ torsion G N).left := by sorry
