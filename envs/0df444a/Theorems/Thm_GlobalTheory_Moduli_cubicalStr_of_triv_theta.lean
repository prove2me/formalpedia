-- Prove2me | Theorems.Thm_GlobalTheory_Moduli_cubicalStr_of_triv_theta
-- name    : GlobalTheory.Moduli.cubicalStr_of_triv_theta
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:25:19.459173+00:00
-- url     : https://prove2.me/theorems/b83db983-fcf7-4ee9-8419-9e89017d2af1
-- title:
--   Moduli: cubical Str of triv theta
-- statement:
--   The Moduli construction uses the cubical Str of triv theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CubicalStrOfTrivTheta.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CubicalStrOfTrivTheta.lean#L15-L21

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubicalOfNormalised
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CubicalStrOfTrivTheta
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
open GlobalTheory GlobalTheory.Moduli

theorem GlobalTheory.Moduli.cubicalStr_of_triv_theta : Out.Laws → ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : LB A.left, M.IsLB → Out.Rigidified A M → Triv (Theta A M) → ∃ L : RigLB A, L.L = M ∧ Nonempty (CubicalStr A L) := by sorry
