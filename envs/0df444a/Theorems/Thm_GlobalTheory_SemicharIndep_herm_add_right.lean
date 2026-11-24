-- Prove2me | Theorems.Thm_GlobalTheory_SemicharIndep_herm_add_right
-- name    : GlobalTheory.SemicharIndep.herm_add_right
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:53:44.86072+00:00
-- url     : https://prove2.me/theorems/5e4d7adb-de7b-49d7-bcca-e05764a96c03
-- title:
--   Semichar Indep: herm add right
-- statement:
--   The Semichar Indep construction uses the herm add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/TorusAtEpsIndep.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/TorusAtEpsIndep.lean#L35-L37

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

theorem GlobalTheory.SemicharIndep.herm_add_right (G : Matrix (Fin r) (Fin r) E) (u v v' : Fin r → E) :
    herm G u (v + v') = herm G u v + herm G u v' := by sorry
