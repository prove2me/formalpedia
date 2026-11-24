-- Prove2me | Theorems.Thm_GlobalTheory_BorelUMod_Cayley_cay_skew
-- name    : GlobalTheory.BorelUMod.Cayley.cay_skew
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:01:06.886432+00:00
-- url     : https://prove2.me/theorems/0496b7e4-e2d0-4cde-a99c-8240232ff185
-- title:
--   Cayley: cay skew
-- statement:
--   The Cayley construction uses the cay skew property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexEqOfSurj.lean#L90-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexEqOfSurj.lean#L90-L106

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

theorem GlobalTheory.BorelUMod.Cayley.cay_skew {c : Fin n → Fin n → ℤ} (hc : IsWeight c) {σ : L →+* L} {t : L} (ht : Valued.v t ≤ 1)
    (hσ : t + σ t = 1) {u : Matrix (Fin n) (Fin n) L} (hu : u - 1 ∈ upLat L c) (huv : u * adjJ σ u = 1) :
    cay t u ∈ skewJ σ n := by sorry
