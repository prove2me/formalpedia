-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsBaseChangeAt_span_range
-- name    : GroundTheory.Arith.SchemeCoh.IsBaseChangeAt.span_range
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:59:01.825546+00:00
-- url     : https://prove2.me/theorems/743452ce-b9c4-43f5-bb40-101c171de44b
-- title:
--   Is Base Change At: span range
-- statement:
--   The Is Base Change At construction uses the span range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/PullbackBaseChange.lean#L226-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/PullbackBaseChange.lean#L226-L238

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_PullbackAffine
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohZariski
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_PullbackBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits
universe u
noncomputable section
variable {W T U : Scheme.{u}}

theorem GroundTheory.Arith.SchemeCoh.IsBaseChangeAt.span_range {g : T ⟶ U} {N : U.Modules} {O : U.Opens}
    (h : IsBaseChangeAt g N O) :
    Submodule.span Γ(T, g ⁻¹ᵁ O) (Set.range (Etale.pullbackUnitApp g N O)) = ⊤ := by sorry
