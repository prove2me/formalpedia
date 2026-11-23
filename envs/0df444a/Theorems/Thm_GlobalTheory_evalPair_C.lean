-- Prove2me | Theorems.Thm_GlobalTheory_evalPair_C
-- name    : GlobalTheory.evalPair_C
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:06.747236+00:00
-- url     : https://prove2.me/theorems/4d6a9549-2260-40bc-816f-02380e0d4bba
-- title:
--   Global Theory: eval Pair C
-- statement:
--   The Global Theory construction uses the eval Pair C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsIsConnectedPrincipalOpen.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsIsConnectedPrincipalOpen.lean#L19-L21

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsConnectedPrincipalOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory

theorem GlobalTheory.evalPair_C {d : ℕ} (z : (Fin d → ℂ) × ℂ) (s : MvPolynomial (Fin d) ℂ) :
    evalPair z (Polynomial.C s) = MvPolynomial.eval z.1 s := by sorry
