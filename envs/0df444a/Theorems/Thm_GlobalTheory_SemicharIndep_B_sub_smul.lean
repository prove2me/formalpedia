-- Prove2me | Theorems.Thm_GlobalTheory_SemicharIndep_B_sub_smul
-- name    : GlobalTheory.SemicharIndep.B_sub_smul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:48:25.046734+00:00
-- url     : https://prove2.me/theorems/b9791d75-f83d-409d-828e-703bd06eaaea
-- title:
--   Semichar Indep: B sub smul
-- statement:
--   The Semichar Indep construction uses the B sub smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/TorusAtEpsIndep.lean#L66-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/TorusAtEpsIndep.lean#L66-L69

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TorusAtEpsIndep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.SemicharIndep
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.SemicharIndep.B_sub_smul (X : Data E r) (a b : E) (u v : Fin r → E) :
    B X u ((a - b) • v) = B X u (a • v) - B X u (b • v) := by sorry
