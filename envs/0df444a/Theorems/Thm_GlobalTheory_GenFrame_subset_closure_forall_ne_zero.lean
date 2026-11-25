-- Prove2me | Theorems.Thm_GlobalTheory_GenFrame_subset_closure_forall_ne_zero
-- name    : GlobalTheory.GenFrame.subset_closure_forall_ne_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:14:31.391783+00:00
-- url     : https://prove2.me/theorems/4f921343-1d0a-4142-a37c-fcb4ea965716
-- title:
--   Gen Frame: subset closure forall ne zero
-- statement:
--   The Gen Frame construction uses the subset closure forall ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/DomSubsetClosureIsGenFrame.lean#L15-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/DomSubsetClosureIsGenFrame.lean#L15-L52

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_BasePsiLeviLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PTNonempty
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GGConn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_ReadingRatioAddition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_DomSubsetClosureIsGenFrame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.GenericFrameParameters
open Cardinal Topology
open GlobalTheory GlobalTheory.GenFrame

theorem GlobalTheory.GenFrame.subset_closure_forall_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U)
    {J : Type*} [Countable J] (f : J → E → ℂ) (hf : ∀ j, DifferentiableOn ℂ (f j) U)
    (hne : ∀ j, ∃ x ∈ U, f j x ≠ 0) : U ⊆ closure {x | x ∈ U ∧ ∀ j, f j x ≠ 0} := by sorry
