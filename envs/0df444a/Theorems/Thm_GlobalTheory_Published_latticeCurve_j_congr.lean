-- Prove2me | Theorems.Thm_GlobalTheory_Published_latticeCurve_j_congr
-- name    : GlobalTheory.Published.latticeCurve_j_congr
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:58:55.52538+00:00
-- url     : https://prove2.me/theorems/c47f2203-6272-4de3-80ec-7b87240ed743
-- title:
--   Published: lattice Curve j congr
-- statement:
--   The Published construction uses the lattice Curve j congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/CmCurveGoodOutsidePrimePremises.lean#L48-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/CmCurveGoodOutsidePrimePremises.lean#L48-L55

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

theorem GlobalTheory.Published.latticeCurve_j_congr {L L' : PeriodPair} (h : L.lattice = L'.lattice) :
    (latticeCurve L).j = (latticeCurve L').j := by sorry
