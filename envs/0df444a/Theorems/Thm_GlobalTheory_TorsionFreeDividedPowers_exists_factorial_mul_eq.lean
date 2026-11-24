-- Prove2me | Theorems.Thm_GlobalTheory_TorsionFreeDividedPowers_exists_factorial_mul_eq
-- name    : GlobalTheory.TorsionFreeDividedPowers.exists_factorial_mul_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:08:36.221231+00:00
-- url     : https://prove2.me/theorems/eb4ad9d0-fa61-4204-8a48-eefbfd977a3d
-- title:
--   Torsion Free Divided Powers: exists factorial mul eq
-- statement:
--   The Torsion Free Divided Powers construction uses the exists factorial mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDividedPowersPrime.lean#L34-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDividedPowersPrime.lean#L34-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDividedPowersPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory GlobalTheory.TorsionFreeDividedPowers
open DividedPowers

theorem GlobalTheory.TorsionFreeDividedPowers.exists_factorial_mul_eq (l : ℕ) (hl : l.Prime) {O : Type} [CommRing O] [IsLocalRing O]
    (hlm : (l : O) ∈ IsLocalRing.maximalIdeal O) (n : ℕ) (hn : n ≠ 0) :
    ∃ q : O, (n.factorial : O) * q = (l : O) ^ (n - 1) := by sorry
