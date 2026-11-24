-- Prove2me | Theorems.Thm_GlobalTheory_IsolatedTheoremFour_main
-- name    : GlobalTheory.IsolatedTheoremFour.main
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:21:26.797959+00:00
-- url     : https://prove2.me/theorems/72573dc3-bc1b-4347-b0b7-fd7414bf1b7d
-- title:
--   Isolated Theorem Four: main
-- statement:
--   The Isolated Theorem Four construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ImportsFurther.lean#L7-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ImportsFurther.lean#L7-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ImportsFurther
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IsolatedTheoremFour
open IsDedekindDomain

theorem GlobalTheory.IsolatedTheoremFour.main : ∀ {K : Type} [inst : Field K] [NumberField K] {l : ℕ}, Nat.Prime l → ∃ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), (↑l : NumberField.RingOfIntegers K) ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v := by sorry
