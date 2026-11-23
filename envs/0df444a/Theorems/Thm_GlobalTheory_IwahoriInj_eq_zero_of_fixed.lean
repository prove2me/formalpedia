-- Prove2me | Theorems.Thm_GlobalTheory_IwahoriInj_eq_zero_of_fixed
-- name    : GlobalTheory.IwahoriInj.eq_zero_of_fixed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:27:42.799751+00:00
-- url     : https://prove2.me/theorems/cffc6760-a30a-4847-b27f-b05fc6f3bfc8
-- title:
--   Iwahori Inj: eq zero of fixed
-- statement:
--   The Iwahori Inj construction uses the eq zero of fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantOrbit.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsLocallyConstantOrbit.lean#L41-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TwistedKernelFixed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantOrbit
import Theorems.Thm_UpperTheory_Reformulated_B_TwistedKernelFixed_eq_zero_of_fixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.IwahoriInj
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem GlobalTheory.IwahoriInj.eq_zero_of_fixed (hπ : IsSmooth π) {H : Subgroup G} (hH : IsCompact (H : Set G)) {v : V}
    (hv : v ∈ fixed π H) (hv' : v ∈ twKer π H 1) : v = 0 := by sorry
