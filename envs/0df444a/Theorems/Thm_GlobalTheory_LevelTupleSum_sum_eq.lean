-- Prove2me | Theorems.Thm_GlobalTheory_LevelTupleSum_sum_eq
-- name    : GlobalTheory.LevelTupleSum.sum_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:19:32.845149+00:00
-- url     : https://prove2.me/theorems/6cbc55d8-f173-47c6-a689-1e6d69e42350
-- title:
--   Level Tuple Sum: sum eq
-- statement:
--   The Level Tuple Sum construction uses the sum eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/LevelTupleSumEqRational.lean#L147-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/LevelTupleSumEqRational.lean#L147-L196

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

theorem GlobalTheory.LevelTupleSum.sum_eq {X : Data E r} {x : Frame X.Ψ r} (hx : x ∈ X.dom) (A : TorusAt X x)
    (𝒯 : Finset (Fin r → Fin r → E)) (h1 : ∀ t ∈ 𝒯, Gen X.Λ t)
    (h2 : ∀ t, Gen X.Λ t → ∃! t', t' ∈ 𝒯 ∧ ∀ j, t j - t' j ∈ X.Λ) (n : ℕ) (hn : n = r) :
    (∑ᶠ (a : Fin n → Vsp A.T.dim) (_ : a ∈ {a : Fin n → Vsp A.T.dim |
      (∀ j, a j ∈ ZSpan.fundamentalDomain A.T.b) ∧ (∀ j, ((5 : ℂ) ^ 2) • a j ∈ A.T.L) ∧
        ∀ x ∈ A.T.L, ∃ c : Fin n → 𝓞 E, ∃ y ∈ A.T.L,
          x = ∑ j, act (c j) (((5 : ℂ) ^ 2) • a j) + (5 : ℂ) • y}),
      ∏ b, A.T.ptN2 1 A.s (fun _ => a b) / A.T.l2 1 A.s) =
      ∑ t ∈ 𝒯, ∏ b, A.T.ptN2 1 A.s (fun _ => A.φ (t b)) / A.T.l2 1 A.s := by sorry
