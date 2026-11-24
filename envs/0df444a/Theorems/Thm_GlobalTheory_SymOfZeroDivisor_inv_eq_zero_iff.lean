-- Prove2me | Theorems.Thm_GlobalTheory_SymOfZeroDivisor_inv_eq_zero_iff
-- name    : GlobalTheory.SymOfZeroDivisor.inv_eq_zero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:11.899096+00:00
-- url     : https://prove2.me/theorems/d3f3a44d-b8ec-4613-ab30-1c0242e2cc24
-- title:
--   Sym Of Zero Divisor: inv eq zero iff
-- statement:
--   The Sym Of Zero Divisor construction uses the inv eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SymmetricLineBundleOfRegularSection.lean#L25-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/SymmetricLineBundleOfRegularSection.lean#L25-L38

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsoLineBundleOfRegularPullbacksSameZeroSchemeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SymmetricLineBundleOfRegularSection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SymOfZeroDivisor

theorem GlobalTheory.SymOfZeroDivisor.inv_eq_zero_iff {S : Scheme.{0}} (A : Over S) [GrpObj A] {T : Scheme.{0}} (t : T ⟶ A.left) :
    t ≫ (GrpObj.inv : A ⟶ A).left = (t ≫ (GrpObj.inv : A ⟶ A).left) ≫ A.hom ≫ eSec A ↔
      t = t ≫ A.hom ≫ eSec A := by sorry
