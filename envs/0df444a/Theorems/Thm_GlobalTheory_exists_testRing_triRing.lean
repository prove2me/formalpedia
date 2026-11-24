-- Prove2me | Theorems.Thm_GlobalTheory_exists_testRing_triRing
-- name    : GlobalTheory.exists_testRing_triRing
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:44:24.197819+00:00
-- url     : https://prove2.me/theorems/05222ca9-f953-48c0-9f68-b1444c1d8079
-- title:
--   Global Theory: exists test Ring tri Ring
-- statement:
--   The Global Theory construction uses the exists test Ring tri Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsTriangularFrameRingOverTestRing.lean#L77-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsTriangularFrameRingOverTestRing.lean#L77-L110

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ReducedFiniteTypeIffTestRing
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsTriangularFrameRingOverTestRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open GlobalTheory

theorem GlobalTheory.exists_testRing_triRing :
    ∀ (K : Type) [Field K] (J : Type) [Fintype J] (m : J → ℕ) (p : TRing K), ∃ (A : TRing K) (π : p.R →ₐ[K] A.R) (X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A.R) (s : (A.R)ˣ), TriRing m π X s := by sorry
