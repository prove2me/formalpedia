-- Prove2me | Theorems.Thm_GlobalTheory_Published_IsIntegersLattice_j_eq
-- name    : GlobalTheory.Published.IsIntegersLattice.j_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:37.029636+00:00
-- url     : https://prove2.me/theorems/63ada8ec-460f-4429-9fc2-197601cd7900
-- title:
--   Is Integers Lattice: j eq
-- statement:
--   The Is Integers Lattice construction uses the j eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/CmCurveGoodOutsidePrimePremises.lean#L57-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/CmCurveGoodOutsidePrimePremises.lean#L57-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_ComplexMultiplicationJPremises
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__CmCurveGoodOutsidePrimePremises_e87ddea43482082e
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain WeierstrassCurve
open scoped nonZeroDivisors IntermediateField
open GlobalTheory GlobalTheory.Published

theorem GlobalTheory.Published.IsIntegersLattice.j_eq {p : ℕ} {L L' : PeriodPair} (h : IsIntegersLattice p L)
    (h' : IsIntegersLattice p L') : (latticeCurve L).j = (latticeCurve L').j := by sorry
