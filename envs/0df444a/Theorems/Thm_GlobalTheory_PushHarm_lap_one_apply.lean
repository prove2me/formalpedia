-- Prove2me | Theorems.Thm_GlobalTheory_PushHarm_lap_one_apply
-- name    : GlobalTheory.PushHarm.lap_one_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:01:51.035728+00:00
-- url     : https://prove2.me/theorems/ac195e39-110a-43b5-a273-e6cdfbf16216
-- title:
--   Push Harm: lap one apply
-- statement:
--   The Push Harm construction uses the lap one apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/PushMemHarmK.lean#L75-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/PushMemHarmK.lean#L75-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_UnitaryDetClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PushMemHarmK
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
open GlobalTheory GlobalTheory.PushHarm
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (c : Coeff l) {n : ℕ}

theorem GlobalTheory.PushHarm.lap_one_apply {T : Type} {r : T → ℕ} {k : Type} [Field k] (τ τ' : T) (a : Fin (r τ))
    (a' : Fin (r τ')) (P : MvPolynomial (Letter T r n) k) :
    lap r n k 1 τ τ' a a' P =
      ∑ b, pderiv (⟨τ, a, b⟩ : Letter T r n) (pderiv (⟨τ', a', b⟩ : Letter T r n) P) := by sorry
