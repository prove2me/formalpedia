-- Prove2me | Theorems.Thm_GlobalTheory_BorelUMod_Cayley_cay_eq
-- name    : GlobalTheory.BorelUMod.Cayley.cay_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:04.86025+00:00
-- url     : https://prove2.me/theorems/d6905644-975c-441c-976b-96c79f5f24d7
-- title:
--   Cayley: cay eq
-- statement:
--   The Cayley construction uses the cay eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexEqOfSurj.lean#L77-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexEqOfSurj.lean#L77-L82

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

theorem GlobalTheory.BorelUMod.Cayley.cay_eq {c : Fin n → Fin n → ℤ} (hc : IsWeight c) {t : L} (ht : Valued.v t ≤ 1)
    {u : Matrix (Fin n) (Fin n) L} (hu : u - 1 ∈ upLat L c) :
    ∃ z ∈ upLat L c, (1 + t • (u - 1)) * (1 + z) = 1 ∧ (1 + z) * (1 + t • (u - 1)) = 1 ∧
      cay t u = (1 + z) * (u - 1) := by sorry
