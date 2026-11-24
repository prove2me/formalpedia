-- Prove2me | Theorems.Thm_GlobalTheory_KernelNoTorsion_eq_of_isSchemeTheoreticallyDominant
-- name    : GlobalTheory.KernelNoTorsion.eq_of_isSchemeTheoreticallyDominant
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:47:32.200612+00:00
-- url     : https://prove2.me/theorems/4e19ddfa-6b66-4a5e-94a4-d7c3348340be
-- title:
--   Kernel No Torsion: eq of is Scheme Theoretically Dominant
-- statement:
--   The Kernel No Torsion construction uses the eq of is Scheme Theoretically Dominant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/EqOneOfPowEqOneOfCompEqOne.lean#L11-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/EqOneOfPowEqOneOfCompEqOne.lean#L11-L20

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KernelNoTorsion

theorem GlobalTheory.KernelNoTorsion.eq_of_isSchemeTheoreticallyDominant {X S Y Z : Scheme.{0}} (f : X ⟶ S) [IsSeparated f]
    {a b : Y ⟶ X} (hab : a ≫ f = b ≫ f) (j : Z ⟶ Y) [IsSchemeTheoreticallyDominant j]
    (hj : j ≫ a = j ≫ b) : a = b := by sorry
