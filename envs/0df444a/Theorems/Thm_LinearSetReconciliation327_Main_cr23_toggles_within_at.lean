-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_cr23_toggles_within_at
-- name    : LinearSetReconciliation327.Main.cr23_toggles_within_at
-- status  : Proved
-- author  : @djwj233
-- created : 2026-11-21T09:46:24.649793+00:00
-- url     : https://prove2.me/theorems/45d6ec9e-5af0-4eca-92a6-3151595619d3
-- title:
--   Proposition 2.3 — the rebased toggle at an arbitrary payload word
-- statement:
--   For the CR23 sparse-recovery sketch, the toggle program of Proposition 2.3, run with its preprocessing table rebased by $\beta$ and with the packed payload stored from word $\beta$ upwards, XORs the column $CR_{N,t}\,e_v$ into that payload in place within $65536\log^2(N+2)$ word operations, halting at its own end and leaving every word outside the payload untouched.
-- source:
--   A. (2026), arXiv:2611.11409, \u00a72.3 (Proposition 2.3); M. Cheraghchi and I. Ribeiro, Simple Codes for Sparse Recovery, arXiv:1901.02852, \u00a71.2 and Definition 2, https://arxiv.org/abs/1901.02852

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_CR23

namespace LinearSetReconciliation327.Main

theorem cr23_toggles_within_at (N t : ℕ) (hN : 1 ≤ N) (htN : t ≤ N)
    (C : Fin N → Fin (cr23D N) → Fin (cr23M t)) (β : ℕ)
    (hβ : β + wordsOf (cr23Word N) (cr23R N t) ≤ 2 ^ cr23Word N) :
∀ (y : Fin (cr23R N t) → ZMod 2) (v : Fin N), ∃ s' : RAMState,
  HaltsWithin progUp (detEnv (cr23Word N) (cr23DecDetAt N t C β))
    (65536 * lg ((N : ℝ) + 2) ^ 2) (payStart (cr23Word N) β y v.val) s' ∧
  (∀ addr < wordsOf (cr23Word N) (cr23R N t),
    s'.mem (β + addr)
      = packMem (cr23Word N) (y + cr23Sketch N t C (Pi.single v 1)) addr) ∧
  s'.pc = 20 ∧ progUp.length = 21 ∧
  (∀ c, (c < β ∨ β + wordsOf (cr23Word N) (cr23R N t) ≤ c) →
    s'.mem c = payMem (cr23Word N) β y c) := by sorry

end LinearSetReconciliation327.Main
