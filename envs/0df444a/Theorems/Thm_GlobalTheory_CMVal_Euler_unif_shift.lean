-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Euler_unif_shift
-- name    : GlobalTheory.CMVal.Euler.unif_shift
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:20:08.814007+00:00
-- url     : https://prove2.me/theorems/ea93b43d-1306-4d0b-b7c7-0a84a022fe2e
-- title:
--   Euler: unif shift
-- statement:
--   The Euler construction uses the unif shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L236-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean#L236-L264

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallLocInShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal Filter Topology
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler
variable {E : Type} [Field E] [NumberField E]
open Classical

theorem GlobalTheory.CMVal.Euler.unif_shift {m : HeightOneSpectrum (OF E) → ℕ} {T : Finset (HeightOneSpectrum (𝓞 E))} {w : HeightOneSpectrum (𝓞 E)}
    (hm : m (w.under (OF E)) = 0) (hw : w ∉ T) (y : (Af E)ˣ) :
    (unifAt w)⁻¹ * y ∈ MS m T ↔ y ∈ MS m T ∧ y ∉ MS m (insert w T) := by sorry
