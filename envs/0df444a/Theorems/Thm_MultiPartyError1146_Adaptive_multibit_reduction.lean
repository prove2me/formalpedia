-- Prove2me | Theorems.Thm_MultiPartyError1146_Adaptive_multibit_reduction
-- name    : MultiPartyError1146.Adaptive.multibit_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T18:34:43.751192+00:00
-- url     : https://prove2.me/theorems/84155466-3fc1-49d6-a118-a531580a5e7e
-- title:
--   Lemma 4.13 — coded multibit reduction
-- statement:
--   There is an absolute $a\ge1$ such that for all positive $n,m,T$, $0<\delta<1$, and every $T$-round one-bit protocol resilient to $\delta$, an outer binary distance-0.49 code of length $\ell\le am$ makes Algorithm 2 satisfy
--   $$T'=\ell T\le amT,\qquad\delta'=0.1\delta.$$
--   The outer encoder is injective and has positive length. This retains the proof's explicit resilience coefficient and ensures correctness under the same factor-10 local criterion. It does not replace the code with uncoded repetition.
--
--   Differences from the source:
--   - encoding: O(mT) rounds and Ω(δ) resilience → one absolute a, outer code length ≤am, actual Algorithm 2 and resilience δ/10; reason: printed p.30 proves 0.1δ, using relative distance 0.49
--   - encoding: one-based party, time and message-coordinate labels → Fin indices, Boolean bits and optional-Boolean received symbols with zero-based iteration indices; reason: fixed finite relabelings preserve every input, action and error; supporting local quantities are execution-derived
-- source:
--   Klim Efremenko, Gillat Kol, Raghuvansh Saxena, Zhijun Zhang, STOC 2027 submission #1146 (October 2026), Lemma 4.13, printed p.30, PDF p.32

import Mathlib
import Definitions.Def_MultiPartyError1146_Adaptive_Reduction

set_option autoImplicit false

namespace MultiPartyError1146.Adaptive

theorem multibit_reduction :
    ∃ a : ℝ, 1 ≤ a ∧ ∀ n m T : ℕ, 1 ≤ n → 1 ≤ m → 1 ≤ T →
      ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ P : Protocol n 1 T, Resilient P δ →
        ∃ C : BinaryCode (Fin m → Bool), 1 ≤ C.length ∧
          (C.length : ℝ) ≤ a * m ∧ Function.Injective C.encode ∧
          C.HasDistance ((49 : ℝ) / 100) ∧
          Resilient (algorithm2 P C) (δ / 10) := by sorry

end MultiPartyError1146.Adaptive
