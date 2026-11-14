-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_wordRAM_word_invariant
-- name    : KSATSingleFlip.Connect.wordRAM_word_invariant
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:08:15.717314+00:00
-- url     : https://prove2.me/theorems/4b9bd5f5-47df-4932-83b2-ecd067f798ae
-- title:
--   Fixed-width word-RAM state invariant
-- statement:
--   In the candidate fixed-width word-RAM model, suppose every register and memory cell initially contains an unsigned $w$-bit word. After any finite number of program steps, every register and memory cell still lies in $[0,2^w)$. This verifies that the unit-cost machine does not silently grow unbounded integer values during execution.
-- source:
--   Formalization choice for the runtime statements of Theorem 1.3, Wang, Yin, Yu, Zhang, Single-Variable Connectivity in Random k-SAT, STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf. The paper does not specify this machine model.

import Definitions.Def_KSATSingleFlip_Connect_WordRAM

namespace KSATSingleFlip.Connect

/-- A valid word-RAM state remains valid under every bounded execution. -/
theorem wordRAM_word_invariant (program : WordRAMProgram) (w T : ℕ) (s : WordRAMState)
    (hr : ∀ r, s.registers r < 2^w) (hm : ∀ a, s.memory a < 2^w) :
    (∀ r, (wordRAMRun program w T s).registers r < 2^w) ∧
    ∀ a, (wordRAMRun program w T s).memory a < 2^w := by
  sorry

end KSATSingleFlip.Connect
