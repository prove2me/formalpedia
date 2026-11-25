-- Prove2me | Theorems.Thm_GlobalTheory_LevelTupleSum_gen_iff
-- name    : GlobalTheory.LevelTupleSum.gen_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:48:05.704182+00:00
-- url     : https://prove2.me/theorems/338f5fb7-c380-4614-a347-9abb3895ee5f
-- title:
--   Level Tuple Sum: gen iff
-- statement:
--   The Level Tuple Sum construction uses the gen iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/LevelTupleSumEqRational.lean#L128-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/LevelTupleSumEqRational.lean#L128-L145

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

theorem GlobalTheory.LevelTupleSum.gen_iff {X : Data E r} {x : Frame X.Ψ r} (hx : x ∈ X.dom) (A : TorusAt X x)
    (t : Fin r → Fin r → E) :
    Gen X.Λ t ↔ (∀ j, ((5 : ℂ) ^ 2) • A.φ (t j) ∈ A.T.L) ∧ ∀ z ∈ A.T.L, ∃ c : Fin r → 𝓞 E, ∃ y ∈ A.T.L,
      z = ∑ j, act (c j) (((5 : ℂ) ^ 2) • A.φ (t j)) + (5 : ℂ) • y := by sorry
