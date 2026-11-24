-- Prove2me | Theorems.Thm_GlobalTheory_quasiFiniteAt_of_isClosed_of_generization
-- name    : GlobalTheory.quasiFiniteAt_of_isClosed_of_generization
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:15:49.005327+00:00
-- url     : https://prove2.me/theorems/6dd4c782-15fd-423f-82d6-fc353081955a
-- title:
--   Global Theory: quasi Finite At of is Closed of generization
-- statement:
--   The Global Theory construction uses the quasi Finite At of is Closed of generization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/QuasiFiniteAtAffineSpaceHomOfVectorOfCoord.lean#L48-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/QuasiFiniteAtAffineSpaceHomOfVectorOfCoord.lean#L48-L70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_QuasiFiniteAtAffineSpaceHomOfVectorOfCoord
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
open GlobalTheory.ZJ
open GlobalTheory

theorem GlobalTheory.quasiFiniteAt_of_isClosed_of_generization {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (x : X) (hx : IsClosed ({x} : Set X)) (h : ∀ y, y ⤳ x → f y = f x → y = x) : f.QuasiFiniteAt x := by sorry
