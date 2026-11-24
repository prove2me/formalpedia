-- Prove2me | Theorems.Thm_GlobalTheory_TorsionFreeDividedPowers_ofFactorialUnits_dpow
-- name    : GlobalTheory.TorsionFreeDividedPowers.ofFactorialUnits_dpow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:08:46.793496+00:00
-- url     : https://prove2.me/theorems/204b7287-2747-4408-b7a2-9a627297b9bb
-- title:
--   Torsion Free Divided Powers: of Factorial Units dpow
-- statement:
--   The Torsion Free Divided Powers construction uses the of Factorial Units dpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDividedPowersPrime.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDividedPowersPrime.lean#L29-L32

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

theorem GlobalTheory.TorsionFreeDividedPowers.ofFactorialUnits_dpow {A : Type} [CommRing A] (h : ∀ n : ℕ, IsUnit (n.factorial : A))
    (J : Ideal A) {n : ℕ} {x : A} (hx : x ∈ J) :
    (ofFactorialUnits h J).dpow n x = Ring.inverse (n.factorial : A) * x ^ n := by sorry
