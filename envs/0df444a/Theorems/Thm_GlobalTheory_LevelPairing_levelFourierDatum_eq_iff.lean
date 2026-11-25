-- Prove2me | Theorems.Thm_GlobalTheory_LevelPairing_levelFourierDatum_eq_iff
-- name    : GlobalTheory.LevelPairing.levelFourierDatum_eq_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:15:01.107116+00:00
-- url     : https://prove2.me/theorems/7c7adac9-9b38-52e3-9820-3cf521fef479
-- title:
--   Level Pairing: level Fourier Datum eq iff
-- statement:
--   The Level Pairing construction uses the level Fourier Datum eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/ZeroNotAdmissibleOfRankPos.lean#L141-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/ZeroNotAdmissibleOfRankPos.lean#L141-L163

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LevelPairing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem GlobalTheory.LevelPairing.levelFourierDatum_eq_iff (c : Coeff l) {n : ℕ} (x0 x0' : Fin n → Dw.La) :
    x0Dat c x0 = x0Dat c x0' ↔ ∀ b, x0 b - x0' b ∈ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La) := by sorry
