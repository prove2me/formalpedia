-- Prove2me | Theorems.Thm_GlobalTheory_SemiAbTorsion_finite_ringHom
-- name    : GlobalTheory.SemiAbTorsion.finite_ringHom
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:54:12.623424+00:00
-- url     : https://prove2.me/theorems/62728d0a-70ea-4554-9000-05e878a57298
-- title:
--   Semi Ab Torsion: finite ring Hom
-- statement:
--   The Semi Ab Torsion construction uses the finite ring Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SemiAbelianTorsionFiniteAndClosedPointFiniteOrde.lean#L47-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SemiAbelianTorsionFiniteAndClosedPointFiniteOrde.lean#L47-L54

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

theorem GlobalTheory.SemiAbTorsion.finite_ringHom (A F : Type) [CommRing A] [CommRing F] [Finite F]
    [Algebra.FiniteType ℤ A] : Finite (A →+* F) := by sorry
