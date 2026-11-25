-- Prove2me | Theorems.Thm_GlobalTheory_range_splitTorusPoint_left
-- name    : GlobalTheory.range_splitTorusPoint_left
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:58:31.172686+00:00
-- url     : https://prove2.me/theorems/a8b10ea4-8ccb-49fb-9876-1ec7c181145d
-- title:
--   Global Theory: range split Torus Point left
-- statement:
--   The Global Theory construction uses the range split Torus Point left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FiniteOfIsClosedSplitTorusOfPowEqOne.lean#L125-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FiniteOfIsClosedSplitTorusOfPowEqOne.lean#L125-L137

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteOfIsClosedSplitTorusOfPowEqOne
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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open GlobalTheory
variable {k : Type} [Field k] {X : Type} [AddCommGroup X]
attribute [local instance] zuAlgebra
open scoped AlgebraMonoidAlgebra

theorem GlobalTheory.range_splitTorusPoint_left (t : Multiplicative X →* kˣ) :
    Set.range (splitTorusPoint t).left = {(torusIso k X).hom (torusPrime t)} := by sorry
