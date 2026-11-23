-- Prove2me | Theorems.Thm_GlobalTheory_FiniteCoverGrowth_eq_nodal
-- name    : GlobalTheory.FiniteCoverGrowth.eq_nodal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:06:47.473532+00:00
-- url     : https://prove2.me/theorems/28a17e0e-ba93-4fff-a9a7-b93aa981b629
-- title:
--   Finite Cover Growth: eq nodal
-- statement:
--   The Finite Cover Growth construction uses the eq nodal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IntegralAndRationalOfPolynomialGrowth.lean#L133-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IntegralAndRationalOfPolynomialGrowth.lean#L133-L138

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IntegralAndRationalOfPolynomialGrowth
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
open GlobalTheory GlobalTheory.FiniteCoverGrowth

theorem GlobalTheory.FiniteCoverGrowth.eq_nodal {P : Polynomial ℂ} (hm : P.Monic) (hs : P.Separable) :
    P = Lagrange.nodal P.roots.toFinset id := by sorry
