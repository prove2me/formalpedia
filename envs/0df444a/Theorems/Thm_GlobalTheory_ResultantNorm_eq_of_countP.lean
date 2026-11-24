-- Prove2me | Theorems.Thm_GlobalTheory_ResultantNorm_eq_of_countP
-- name    : GlobalTheory.ResultantNorm.eq_of_countP
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:21:26.246186+00:00
-- url     : https://prove2.me/theorems/e8133986-d764-4b86-b91c-c6240ee69153
-- title:
--   Resultant Norm: eq of count P
-- statement:
--   The Resultant Norm construction uses the eq of count P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqOfNormResultantEq.lean#L33-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/EqOfNormResultantEq.lean#L33-L94

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

theorem GlobalTheory.ResultantNorm.eq_of_countP {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    [DecidableEq Ω] (n : ℕ) : ∀ (a b : Multiset Ω) (P Q : K[X]), a.card = n →
      P.map (algebraMap K Ω) = (a.map fun x => X - C x).prod →
      Q.map (algebraMap K Ω) = (b.map fun x => X - C x).prod →
      (∀ G : K[X], a.countP (fun x => aeval x G = 0) = b.countP (fun x => aeval x G = 0)) →
      P = Q := by sorry
