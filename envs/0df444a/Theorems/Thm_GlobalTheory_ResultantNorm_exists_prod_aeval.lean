-- Prove2me | Theorems.Thm_GlobalTheory_ResultantNorm_exists_prod_aeval
-- name    : GlobalTheory.ResultantNorm.exists_prod_aeval
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:22:52.581546+00:00
-- url     : https://prove2.me/theorems/fb303003-7b68-461d-9b4c-ac42de163478
-- title:
--   Resultant Norm: exists prod aeval
-- statement:
--   The Resultant Norm construction uses the exists prod aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqOfNormResultantEq.lean#L16-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqOfNormResultantEq.lean#L16-L31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfNormResultantEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
open GlobalTheory.ResultantNorm
open Polynomial Filter Topology

theorem GlobalTheory.ResultantNorm.exists_prod_aeval {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (a : Multiset Ω)
    (P : K[X]) (hP : P.map (algebraMap K Ω) = (a.map fun x => X - C x).prod) (F : K[X]) :
    ∃ u : K, algebraMap K Ω u = (a.map fun x => aeval x F).prod := by sorry
