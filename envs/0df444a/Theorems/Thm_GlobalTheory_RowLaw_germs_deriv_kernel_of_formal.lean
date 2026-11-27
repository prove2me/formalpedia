-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_germs_deriv_kernel_of_formal
-- name    : GlobalTheory.RowLaw.germs_deriv_kernel_of_formal
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-27T06:16:29.51619+00:00
-- url     : https://prove2.me/theorems/3a4504c8-8ba8-5d08-93e1-0d8615f2bee1
-- title:
--   Row Law: germs deriv kernel of formal
-- statement:
--   The Row Law construction uses the germs deriv kernel of formal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GermsDerivKernelOfFormal.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GermsDerivKernelOfFormal.lean#L18-L24

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IsIntegralGaugedFormalGroupLawPairDataStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntegralGermsIndependentOfCurveSystemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugeDerivEqPairingOfIntegralGaugedLawStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugedFormalGroupKernelSmallOfSecondStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GermsDerivKernelOfFormal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.RowLaw

theorem GlobalTheory.RowLaw.germs_deriv_kernel_of_formal : IntegralGermIndependentAllCharts ∧ CEqFBSt ∧ IndependenceBoundAllCharts := by sorry
