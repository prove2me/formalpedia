-- Prove2me | Theorems.Thm_GlobalTheory_map_minpoly_dvd_of_aeval_one_tmul
-- name    : GlobalTheory.map_minpoly_dvd_of_aeval_one_tmul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:56:38.868203+00:00
-- url     : https://prove2.me/theorems/5be03267-f1dc-4a26-b603-8fab02a20eb9
-- title:
--   Global Theory: map minpoly dvd of aeval one tmul
-- statement:
--   The Global Theory construction uses the map minpoly dvd of aeval one tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/IsIntegralIffMemSpanOneTmulIntegralClosure.lean#L33-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/IsIntegralIffMemSpanOneTmulIntegralClosure.lean#L33-L62

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

theorem GlobalTheory.map_minpoly_dvd_of_aeval_one_tmul {F F' L : Type} [Field F] [Field F'] [Algebra F F']
    [Field L] [Algebra F L] {l : L} (hl : IsIntegral F l) {q : F'[X]}
    (hq : aeval ((1 : F') ⊗ₜ[F] l) q = 0) : (minpoly F l).map (algebraMap F F') ∣ q := by sorry
