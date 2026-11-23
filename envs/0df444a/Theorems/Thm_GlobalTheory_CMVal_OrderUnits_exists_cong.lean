-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_OrderUnits_exists_cong
-- name    : GlobalTheory.CMVal.OrderUnits.exists_cong
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:57:43.285794+00:00
-- url     : https://prove2.me/theorems/d9b78910-5829-45dc-90d0-25f1b4639d0e
-- title:
--   Order Units: exists cong
-- statement:
--   The Order Units construction uses the exists cong property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinPartEqOneOfLevel.lean#L38-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinPartEqOneOfLevel.lean#L38-L68

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfLevel
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
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.OrderUnits
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMVal.OrderUnits.exists_cong {c : Ideal (OF E)} (v : HeightOneSpectrum (OF E)) (n : ℕ) (hn : v.asIdeal ^ n ∣ c)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (hS : ∀ P ∈ S, Over P v) {z : Af E} (hz : z ∈ hatO c) :
    ∃ a : OF E, ∀ P ∈ S, Valued.v (algebraMap E (Af E) (algebraMap (OF E) E a) P - z P) ≤ WithZero.exp (-(n : ℤ)) := by sorry
