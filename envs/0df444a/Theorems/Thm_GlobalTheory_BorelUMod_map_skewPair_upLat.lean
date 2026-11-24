-- Prove2me | Theorems.Thm_GlobalTheory_BorelUMod_map_skewPair_upLat
-- name    : GlobalTheory.BorelUMod.map_skewPair_upLat
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:03:11.877193+00:00
-- url     : https://prove2.me/theorems/e4f7d1c0-dac6-4fde-b1a7-95f64e3043e4
-- title:
--   Borel UMod: map skew Pair up Lat
-- statement:
--   The Borel UMod construction uses the map skew Pair up Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexUpLatEqSq.lean#L37-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexUpLatEqSq.lean#L37-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqSq
import Theorems.Thm_GlobalTheory_LGrp_LeviDatum_IsOpposite_prod

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
variable [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.BorelUMod.map_skewPair_upLat {σ : L →+* L} (hσ : ∀ x, σ (σ x) = x) (hv : ∀ x, Valued.v (σ x) = Valued.v x)
    {θ d : L} (hθ : Valued.v θ ≤ 1) (hθ1 : θ + σ θ = 1) (hd : Valued.v d = 1) (hd1 : σ d = -d)
    {c : Fin n → Fin n → ℤ} (hc : ∀ i j, c j.rev i.rev = c i j) :
    (upLat L c).map (skewPair σ θ d) = (upLat L c ⊓ skewJ σ n).prod (upLat L c ⊓ skewJ σ n) := by sorry
