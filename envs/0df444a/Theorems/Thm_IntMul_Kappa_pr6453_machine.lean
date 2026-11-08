-- Prove2me | Theorems.Thm_IntMul_Kappa_pr6453_machine
-- name    : IntMul.Kappa.pr6453_machine
-- status  : Open
-- author  : @gustasmickus
-- created : 2026-11-08T00:24:15.937372+00:00
-- url     : https://prove2.me/theorems/60f34c9f-b0e4-48d7-90da-2f7482679c50
-- title:
--   Machine-level form of the community construction at $\kappa = 0.003287014$ (PR #6453)
-- statement:
--   There are one deterministic multitape Turing machine $M$, in the model of `Def_IntMul_MultitapeModel`, a real exponent saving $g > 0.003287014$, and constants $C > 0$, $A \in \mathbb{N}$, $n_0 \in \mathbb{N}$ such that
--
--   1. for every $n \ge 1$ and every pair of $n$-bit strings $x,y$, the machine halts on input $x\#y$ with the output $\bin_{2n}(\val x \cdot \val y)$, in some finite number of steps; and
--   2. the number of steps is at most
--   $$C\, n\, (\lg n)^{1-g}\, \bigl(\log \lg n + 1\bigr)^{A}$$
--   for every $n \ge n_0$, where $\lg n = \max(\lceil \log_2 n\rceil, 1)$.
--
--   This is the machine-level form of the community construction whose exponent saving is $\kappa = 0.003287014$ — PR #6453 of `CrocSwap/integer-mult-bounds`, a third group-1091 anchor stacked on the clean mixed-root composition of PR #6417. In the source, that construction is a finite certificate stated conditionally on five inherited framework assumptions: the all-width native claims, the owned-erasure discipline, the compiler, the precision tape, and analytic recovery. None of these is a statement about a Turing machine, while the campaign's formal goal is the full bound with no assumed framework. This node is the transcription of those five assumptions, together with the construction's own cost invoices, into the machine and cost model of `Def_IntMul_MultitapeModel`.
--
--   The statement allows a polylogarithmic overhead $(\log \lg n)^{A}$ and a saving $g$ strictly above the advertised $0.003287014$, which is the form in which any recursive multiplication algorithm's cost analysis terminates: the block bookkeeping produces the logarithmic factor, and the exponent margin is what absorbs it. Applied through the platform lemma `IntMul.Kappa.kappaBound_of_polylog_slack`, this node yields `IntMul.Kappa.KappaBound (0.003287014)`.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453 (third group-1091 anchor on the PR #6417 mixed-root composition), https://github.com/CrocSwap/integer-mult-bounds/pull/6453 , on the pinned revision https://github.com/CrocSwap/integer-mult-bounds/tree/56b66d58297deca1d7dd130247d720e960f77a37 . The five framework assumptions of the source (native_all_columns, owned_erasure, compiler, precision_tape, analytic_recovery) are what this node asserts, transcribed into the multitape-machine cost model of Def_IntMul_MultitapeModel.

import Definitions.Def_IntMul_MultitapeModel

set_option autoImplicit false

namespace IntMul.Kappa

theorem pr6453_machine :
    ∃ (M : MultitapeTM) (g C : ℝ) (A n₀ : ℕ),
      0.003287014 < g ∧ 0 < C ∧
      (∀ n : ℕ, 1 ≤ n → ∃ T : ℝ, MultipliesAt M n T) ∧
      (∀ n : ℕ, n₀ ≤ n →
        MultipliesAt M n (C * n * (lg n : ℝ) ^ (1 - g) * (Real.log (lg n) + 1) ^ A)) := by
  sorry

end IntMul.Kappa
