-- Prove2me | Theorems.Thm_GlobalTheory_BorelUMod_Cayley_cay_surj
-- name    : GlobalTheory.BorelUMod.Cayley.cay_surj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:01:29.345795+00:00
-- url     : https://prove2.me/theorems/7a51f0fa-3104-4ade-9e25-e0bfe93e279d
-- title:
--   Cayley: cay surj
-- statement:
--   The Cayley construction uses the cay surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexEqOfSurj.lean#L128-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexEqOfSurj.lean#L128-L155

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowApplyEqZeroOfStrictUpper
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexEqOfSurj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.LGrp GlobalTheory.BorelUMod Formalism.UG
noncomputable section
open GlobalTheory GlobalTheory.BorelUMod GlobalTheory.BorelUMod.Cayley
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem GlobalTheory.BorelUMod.Cayley.cay_surj {c : Fin n → Fin n → ℤ} (hc : IsWeight c) {σ : L →+* L} (hσσ : ∀ x, σ (σ x) = x) {t : L}
    (ht : Valued.v t ≤ 1) (hσ : t + σ t = 1) {X : Matrix (Fin n) (Fin n) L} (hX : X ∈ upLat L c)
    (hs : X ∈ skewJ σ n) : ∃ u, u - 1 ∈ upLat L c ∧ adjJ σ u * u = 1 ∧ cay t u = X := by sorry
