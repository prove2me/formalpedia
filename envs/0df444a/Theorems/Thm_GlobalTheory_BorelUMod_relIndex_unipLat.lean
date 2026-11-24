-- Prove2me | Theorems.Thm_GlobalTheory_BorelUMod_relIndex_unipLat
-- name    : GlobalTheory.BorelUMod.relIndex_unipLat
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:28:09.117799+00:00
-- url     : https://prove2.me/theorems/7e9cd8e5-919a-4b1f-ba73-05ff15bd9b60
-- title:
--   Borel UMod: rel Index unip Lat
-- statement:
--   The Borel UMod construction uses the rel Index unip Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIdealWeight.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIdealWeight.lean#L22-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_RelIndexMulMeasure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexEqOfSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnipLatIsOpenIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsTerTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdealWeight
import Theorems.Thm_GlobalTheory_BorelUMod_Cayley_relIndex_unipLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp Formalism.UG
open scoped NNReal
noncomputable section
open GlobalTheory GlobalTheory.BorelUMod
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem GlobalTheory.BorelUMod.relIndex_unipLat {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) {c C : Fin n → Fin n → ℤ}
    (hc : IsWeight c) (hC : IsWeight C) (hI : IsIdealWeight c C) :
    (unipLat h.2.1 hC).relIndex (unipLat h.2.1 hc) = q ^ ∑ p ∈ upPairs n, (C p.1 p.2 - c p.1 p.2).toNat := by sorry
