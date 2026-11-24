-- Prove2me | Theorems.Thm_GlobalTheory_SemiAbTorsion_finite_pow_eq_one_of_extension
-- name    : GlobalTheory.SemiAbTorsion.finite_pow_eq_one_of_extension
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:18.438546+00:00
-- url     : https://prove2.me/theorems/16e28db4-1be1-4795-b478-ca2256771670
-- title:
--   Semi Ab Torsion: finite pow eq one of extension
-- statement:
--   The Semi Ab Torsion construction uses the finite pow eq one of extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SemiAbelianTorsionFiniteAndClosedPointFiniteOrde.lean#L14-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SemiAbelianTorsionFiniteAndClosedPointFiniteOrde.lean#L14-L33

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_JacobsonClosedPointsToolsInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SemiAbelianTorsionFiniteAndClosedPointFiniteOrde
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.SemiAbTorsion

theorem GlobalTheory.SemiAbTorsion.finite_pow_eq_one_of_extension {T G B : Type*} [Group T] [CommGroup G] [Group B]
    (i : T →* G) (q : G →* B) (hi : Function.Injective i) (hk : ∀ x, q x = 1 → ∃ t, i t = x)
    (n : ℕ) (hT : Finite {t : T // t ^ n = 1}) (hB : Finite {b : B // b ^ n = 1}) :
    Finite {x : G // x ^ n = 1} := by sorry
