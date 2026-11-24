-- Prove2me | Theorems.Thm_GlobalTheory_BorelUMod_UpLatIndex_relIndex_upLat
-- name    : GlobalTheory.BorelUMod.UpLatIndex.relIndex_upLat
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:01:59.755568+00:00
-- url     : https://prove2.me/theorems/154d0501-d033-4b97-9fca-c31d63ad7ba8
-- title:
--   Up Lat Index: rel Index up Lat
-- statement:
--   The Up Lat Index construction uses the rel Index up Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexUpLatEqProd.lean#L119-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexUpLatEqProd.lean#L119-L125

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqProd
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
open GlobalTheory GlobalTheory.BorelUMod GlobalTheory.BorelUMod.UpLatIndex
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.BorelUMod.UpLatIndex.relIndex_upLat : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L)
    (q n : ℕ), IsUnramInv ϖ σ q → ∀ (c C : Fin n → Fin n → ℤ), (∀ i j, i < j → c i j ≤ C i j) →
    (upLat L C).relIndex (upLat L c) = ∏ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2),
      (q ^ 2) ^ (C p.1 p.2 - c p.1 p.2).toNat := by sorry
