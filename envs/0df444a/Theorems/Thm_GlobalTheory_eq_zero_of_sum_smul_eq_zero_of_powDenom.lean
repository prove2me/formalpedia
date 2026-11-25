-- Prove2me | Theorems.Thm_GlobalTheory_eq_zero_of_sum_smul_eq_zero_of_powDenom
-- name    : GlobalTheory.eq_zero_of_sum_smul_eq_zero_of_powDenom
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:53:26.939475+00:00
-- url     : https://prove2.me/theorems/2f160b4b-1b65-4d9d-9fa5-64381d2c391d
-- title:
--   Global Theory: eq zero of sum smul eq zero of pow Denom
-- statement:
--   The Global Theory construction uses the eq zero of sum smul eq zero of pow Denom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIsUnitMatrixOfPowSmulSpanInvert.lean#L23-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIsUnitMatrixOfPowSmulSpanInvert.lean#L23-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIsUnitMatrixOfPowSmulSpanInvert
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.eq_zero_of_sum_smul_eq_zero_of_powDenom {S EE W RW Y : Type} [CommRing S] [CommRing EE]
    [CommRing W] [CommRing RW] [AddCommGroup Y] [Module RW Y] (a : S →+* EE) (ι : EE →+* RW)
    (c : W →+* RW) (ψ : S →+* W) (Q : S) (hι : Function.Injective ι)
    (hc : ∀ s, ι (a s) = c (ψ s)) (hQ : IsUnit (a Q)) {q : ℕ} (x : Fin q → Y)
    (hx : ∀ w : Fin q → W, ∑ i, c (w i) • x i = 0 → w = 0) (E : Fin q → EE)
    (hE : ∀ m, E m ∈ powDenomSubring a Q) (h0 : ∑ m, ι (E m) • x m = 0) (m : Fin q) :
    E m = 0 := by sorry
