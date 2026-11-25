-- Prove2me | Theorems.Thm_GlobalTheory_LevelTupleSum_Gen_of_sub
-- name    : GlobalTheory.LevelTupleSum.Gen.of_sub
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:24:31.476294+00:00
-- url     : https://prove2.me/theorems/3d0d7942-94d5-442c-b906-72cfe99271a9
-- title:
--   Gen: of sub
-- statement:
--   The Gen construction uses the of sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/LevelTupleSumEqRational.lean#L31-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/LevelTupleSumEqRational.lean#L31-L44

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LevelTupleSumEqRational
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.LevelTupleSum
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
omit [IsCMField E]

theorem GlobalTheory.LevelTupleSum.Gen.of_sub {Λ : Submodule (𝓞 E) (Fin r → E)} {t t' : Fin r → Fin r → E} (h : Gen Λ t)
    (hs : ∀ j, t j - t' j ∈ Λ) : Gen Λ t' := by sorry
