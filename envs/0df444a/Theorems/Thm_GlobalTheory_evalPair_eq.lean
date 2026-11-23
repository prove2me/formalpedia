-- Prove2me | Theorems.Thm_GlobalTheory_evalPair_eq
-- name    : GlobalTheory.evalPair_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:13:29.22516+00:00
-- url     : https://prove2.me/theorems/b4cc2737-8c3c-454c-ab0e-dc900bc6e519
-- title:
--   Global Theory: eval Pair eq
-- statement:
--   The Global Theory construction uses the eval Pair eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsIsConnectedPrincipalOpen.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsIsConnectedPrincipalOpen.lean#L15-L17

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

theorem GlobalTheory.evalPair_eq {d : ℕ} (z : (Fin d → ℂ) × ℂ) (r : Polynomial (MvPolynomial (Fin d) ℂ)) :
    evalPair z r = (r.map (MvPolynomial.eval z.1)).eval z.2 := by sorry
