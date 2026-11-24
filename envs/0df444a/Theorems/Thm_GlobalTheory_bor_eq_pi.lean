-- Prove2me | Theorems.Thm_GlobalTheory_bor_eq_pi
-- name    : GlobalTheory.bor_eq_pi
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:07:02.513875+00:00
-- url     : https://prove2.me/theorems/3baa570c-a783-49e5-82ce-93f37cfd656a
-- title:
--   Global Theory: bor eq pi
-- statement:
--   The Global Theory construction uses the bor eq pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ContinuousRmulPair.lean#L15-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ContinuousRmulPair.lean#L15-L40

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_QuotientIsHausdorff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OmFConnPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ContinuousRmulPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [NumberField E] [IsCMField E]

theorem GlobalTheory.bor_eq_pi (Ψ : Finset (E →+* ℂ)) (r : ℕ) :
    Bor Ψ r = Set.univ.pi fun _ : Ψ => Set.univ.pi fun a : Fin r => Set.univ.pi fun c : Fin r =>
      if c < a then ({0} : Set ℂ) else if c = a then ({0}ᶜ : Set ℂ) else Set.univ := by sorry
