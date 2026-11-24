-- Prove2me | Theorems.Thm_GlobalTheory_BorelUMod_skewPair_injective
-- name    : GlobalTheory.BorelUMod.skewPair_injective
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:02:18.061252+00:00
-- url     : https://prove2.me/theorems/69df53fb-0586-418e-8f46-e70058b32199
-- title:
--   Borel UMod: skew Pair injective
-- statement:
--   The Borel UMod construction uses the skew Pair injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexUpLatEqSq.lean#L26-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexUpLatEqSq.lean#L26-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqSq
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
open GlobalTheory GlobalTheory.BorelUMod
variable {L : Type} [Field L] {n : ℕ}

theorem GlobalTheory.BorelUMod.skewPair_injective (σ : L →+* L) (θ : L) {d : L} (hd : d ≠ 0) :
    Function.Injective (skewPair (n := n) σ θ d) := by sorry
