-- Prove2me | Theorems.Thm_GlobalTheory_mem_range_of_map_eq_of_isLocalHom
-- name    : GlobalTheory.mem_range_of_map_eq_of_isLocalHom
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:56:12.042253+00:00
-- url     : https://prove2.me/theorems/6bc328b1-2318-4805-8d4c-365ed4f8acf9
-- title:
--   Global Theory: mem range of map eq of is Local Hom
-- statement:
--   The Global Theory construction uses the mem range of map eq of is Local Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/IsIntegralIffMemSpanOneTmulIntegralClosure.lean#L12-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/IsIntegralIffMemSpanOneTmulIntegralClosure.lean#L12-L31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsIntegralIffMemSpanOneTmulIntegralClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open Polynomial
open GlobalTheory

theorem GlobalTheory.mem_range_of_map_eq_of_isLocalHom {R R' F F' : Type} [CommRing R] [IsDomain R]
    [ValuationRing R] [CommRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')]
    [Field F] [Algebra R F] [IsFractionRing R F] [Field F'] [Algebra R' F'] [IsFractionRing R' F']
    [Algebra F F'] [Algebra R F'] [IsScalarTower R F F'] [IsScalarTower R R' F']
    (c : F) (r' : R') (h : algebraMap R' F' r' = algebraMap F F' c) :
    ∃ r : R, algebraMap R F r = c := by sorry
