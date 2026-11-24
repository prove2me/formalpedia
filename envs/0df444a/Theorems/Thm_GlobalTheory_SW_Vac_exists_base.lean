-- Prove2me | Theorems.Thm_GlobalTheory_SW_Vac_exists_base
-- name    : GlobalTheory.SW.Vac.exists_base
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:45:25.018299+00:00
-- url     : https://prove2.me/theorems/06fd79b4-d08c-495f-9ff8-5a2cbd557f17
-- title:
--   Vac: exists base
-- statement:
--   The Vac construction uses the exists base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsExOfPow.lean#L205-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsExOfPow.lean#L205-L250

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Vac
noncomputable section
variable {κ ι : Type} [Fintype κ] [Fintype ι]

theorem GlobalTheory.SW.Vac.exists_base (A : AddSubgroup (Matrix κ ι ℚ × Matrix κ ι ℚ))
    (ε : Matrix κ ι ℚ × Matrix κ ι ℚ → ℂ) (hA : A.FG)
    (hε : ∀ y ∈ A, ∀ y' ∈ A, ε (y + y') = ε y * ε y' * ex (pr y.1 y'.2 - pr y'.1 y.2))
    {m : ℕ} (hm : 0 < m) (hm' : ∀ y ∈ A, ε (m • y) = 1) :
    ∃ x₀, ∀ a, (a, 0) ∈ A → ε (a, 0) * ex (2 * pr x₀ a) = 1 := by sorry
