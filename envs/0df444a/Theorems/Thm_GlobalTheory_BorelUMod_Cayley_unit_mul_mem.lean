-- Prove2me | Theorems.Thm_GlobalTheory_BorelUMod_Cayley_unit_mul_mem
-- name    : GlobalTheory.BorelUMod.Cayley.unit_mul_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:01:18.303435+00:00
-- url     : https://prove2.me/theorems/93d8461b-968e-494b-8d4b-16cb547bc64f
-- title:
--   Cayley: unit mul mem
-- statement:
--   The Cayley construction uses the unit mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexEqOfSurj.lean#L59-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexEqOfSurj.lean#L59-L64

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

theorem GlobalTheory.BorelUMod.Cayley.unit_mul_mem {c C : Fin n → Fin n → ℤ} (hI : IsIdealWeight c C) {a b x : Matrix (Fin n) (Fin n) L}
    (ha : a ∈ upLat L c) (hb : b ∈ upLat L c) (hx : x ∈ upLat L C) : (1 + a) * x * (1 + b) ∈ upLat L C := by sorry
