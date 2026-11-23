-- Prove2me | Theorems.Thm_GlobalTheory_SW_TwistAdm_single_mem_std
-- name    : GlobalTheory.SW.TwistAdm.single_mem_std
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:47:54.667692+00:00
-- url     : https://prove2.me/theorems/4a15ee3c-fd06-487f-bb5d-5661cbff6745
-- title:
--   Twist Adm: single mem std
-- statement:
--   The Twist Adm construction uses the single mem std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/TwistAdmissible.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/TwistAdmissible.lean#L25-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.TwistAdm
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real Classical
variable {E : Type} [Field E] [NumberField E] {n N : ℕ}

theorem GlobalTheory.SW.TwistAdm.single_mem_std (a : Fin N) :
    (Pi.single a 1 : Fin N → E) ∈ _root_.GlobalTheory.SW.stdL E N := by sorry
