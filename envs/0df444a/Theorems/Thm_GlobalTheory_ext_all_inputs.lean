-- Prove2me | Theorems.Thm_GlobalTheory_ext_all_inputs
-- name    : GlobalTheory.ext_all_inputs
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:47:28.437147+00:00
-- url     : https://prove2.me/theorems/59f0d44c-b0c7-468a-a9e8-d8bb4eb7394f
-- title:
--   Global Theory: ext all inputs
-- statement:
--   The Global Theory construction uses the ext all inputs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/ExtAllInputs.lean#L136-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/ExtAllInputs.lean#L136-L140

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_SupLeL2PrincipalTorus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_GaussTailOfCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsOrthonormalOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_NearestPlaneRounding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ExtAllInputs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory

theorem GlobalTheory.ext_all_inputs : _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.All := by sorry
