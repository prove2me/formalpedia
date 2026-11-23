-- Prove2me | Theorems.Thm_GlobalTheory_KernelNoTorsion_torsion_hom_ext
-- name    : GlobalTheory.KernelNoTorsion.torsion_hom_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:43:29.582021+00:00
-- url     : https://prove2.me/theorems/3c429b28-ba96-43d1-8885-9e1e9b322dbb
-- title:
--   Kernel No Torsion: torsion hom ext
-- statement:
--   The Kernel No Torsion construction uses the torsion hom ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/EqOneOfPowEqOneOfCompEqOne.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/EqOneOfPowEqOneOfCompEqOne.lean#L52-L54

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

theorem GlobalTheory.KernelNoTorsion.torsion_hom_ext {S : Scheme.{0}} {Y G : Over S} [GrpObj G] {n : ℕ}
    {a b : Y ⟶ torsion G n} (h : a ≫ torsion.ι G n = b ≫ torsion.ι G n) : a = b := by sorry
