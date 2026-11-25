-- Prove2me | Theorems.Thm_GlobalTheory_ChF_fh_gmF
-- name    : GlobalTheory.ChF.fh_gmF
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T18:01:07.333801+00:00
-- url     : https://prove2.me/theorems/c4b7beb5-5161-4a17-a178-c8b071392046
-- title:
--   Ch F: fh gm F
-- statement:
--   The Ch F construction uses the fh gm F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MultiplicativeFormalGroupLawPowerPTorsionFiniteF.lean#L106-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MultiplicativeFormalGroupLawPowerPTorsionFiniteF.lean#L106-L182

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GmLawCharsMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesExistsPolynomialTotalDegreeLeSubMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_MvPowerSeriesEvalOfPowMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MultiplicativeFormalGroupLawPowerPTorsionFiniteF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.ChF
open GlobalTheory GlobalTheory.ChF

theorem GlobalTheory.ChF.fh_gmF : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (r : ℕ), FH p (gmF O r) := by sorry
