-- Prove2me | Theorems.Thm_GlobalTheory_ZH_WtLin_app_constFn
-- name    : GlobalTheory.ZH.WtLin.app_constFn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:13:12.464492+00:00
-- url     : https://prove2.me/theorems/d83797b0-f14d-46f5-b6ef-010d782f2666
-- title:
--   Wt Lin: app const Fn
-- statement:
--   The Wt Lin construction uses the app const Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/CoeffSymmSum.lean#L25-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/CoeffSymmSum.lean#L25-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CoeffSymmSum
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.WtLin

theorem GlobalTheory.ZH.WtLin.app_constFn {R : Type} [CommRing R] {X Y : Scheme.{0}} (q : X ⟶ Sp R) (q' : Y ⟶ Sp R) (f : Y ⟶ X)
    (hf : f ≫ q = q') (U : X.Opens) (a : R) :
    (f.app U).hom (constFn q U a) = constFn q' (f ⁻¹ᵁ U) a := by sorry
