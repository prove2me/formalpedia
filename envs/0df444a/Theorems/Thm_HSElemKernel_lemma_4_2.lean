-- Prove2me | Theorems.Thm_HSElemKernel_lemma_4_2
-- name    : HSElemKernel.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:24:56.327302+00:00
-- url     : https://prove2.me/theorems/7e2f5483-a9b3-4ee2-9f3d-68ea19a8a22e
-- title:
--   Lemma 4.2 — sampling $\mathcal F$ with $B = O(k/\log k)$, $q_2 = O(\log^2 k)$, $t = O(\log k)$ separating each $T$ w.p. $\ge 3/4$
-- statement:
--   Let $W$ be a finite set and $k \ge 2$. There is an expected polynomial-time randomized algorithm that samples a two-level hash pair $\mathcal F = (\tilde h, \mathcal H_2)$ on $W$ with
--   $$B = O(k / \log k), \qquad q_2 = O(\log^2 k), \qquad t = O(\log k)$$
--   such that, for every fixed set $T \subseteq W$ with $|T| \le k$, $\mathcal F$ separates $T$ with probability at least $3/4$.
--
--   Precisely: there are a program $P$ with fair coins and constants $C > 0$, $K$ such that for all $w$ and $k \ge 2$, on input $[w, k]$ (with $W = \{0, \dots, w-1\}$):
--
--   1. the expected bit cost is at most $C(w + |k| + 2)^K$, and on every coin sequence on which the run halts, the output decodes to a pair $\mathcal F$ with $B \le Ck/\log_2 k$, $q_2 \le C\log_2^2 k$, $t \le C\log_2 k$;
--   2. for every $T \subseteq W$ with $|T| \le k$, the event that the run halts and its output separates $T$ is measurable and has probability at least $3/4$.
--
--   Together with Lemma 4.4 this gives the success probability of the randomized encoding.
--
--   **Formalization Note** The paper names no machine model. Running times are measured on the published logarithmic-cost RAM with fair coins (`TimeSpaceMA_RAM`, with the cost layer `SoftmaxAttnFD_Machine`): every executed instruction costs one plus the bit lengths of the addresses and values it touches. Inputs are lists of natural numbers placed in memory from cell $0$; outputs are read from memory (cell $0$ holds the output length) through a fixed strict decoder.
--
--   Differences from the source:
--   - reading: k, the parameter of the instance → hypothesis k ≥ 2; reason: Section 2.1 makes k ≥ 2 before the encoding; k/log k is undefined at k = 1
--   - encoding: expected polynomial-time algorithm on an unnamed machine → program of the published log-cost RAM with fair coins; expected bit cost ≤ C(w + |k| + 2)^K on input [w, k]; reason: the input is the set W (w elements) and the number k; polynomially equivalent models give the same class
--   - encoding: B = O(k/log k), q₂ = O(log² k), t = O(log k) for the sampled pair → B ≤ C k/log₂ k, q₂ ≤ C log₂² k, t ≤ C log₂ k on every halting coin sequence, output read by decodeHash; reason: O(·) with an explicit constant; the bounds hold for every sample
--   - encoding: "with probability at least 3/4" → the coin-tape measure of the measurable event {halts and separates T} is ≥ 3/4; reason: the expected-cost bound forces halting with probability one
-- source:
--   Sheng–Xiao, A Near-Linear Element-Kernel for d-Hitting Set, arXiv:2609.06512 (held version, sha256 aca9c70e…), Lemma 4.2, p.9

import Mathlib
import Definitions.Def_SoftmaxAttnFD_Machine
import Definitions.Def_HSElemKernel_Separates
import Definitions.Def_HSElemKernel_decodeHash
import Definitions.Def_HSElemKernel_outputList
import Definitions.Def_HSElemKernel_bitLen

open MeasureTheory
open scoped ENNReal

namespace HSElemKernel

/-- **Lemma 4.2** (two-level random hashing; Sheng–Xiao, *A Near-Linear Element-Kernel for d-Hitting Set*, arXiv:2609.06512 (held version, sha256 aca9c70e…), Lemma 4.2, p.9): for a finite set `W`, an
expected polynomial-time algorithm samples a pair `F = (h̃, H₂)` with `B = O(k / log k)`,
`q₂ = O(log² k)`, `t = O(log k)`, such that for every fixed `T ⊆ W` with `|T| ≤ k`, `F`
separates `T` with probability at least `3/4`.

There are a program `P` of the published log-cost RAM with fair coins and constants `C, K`
such that for all `w` and `k ≥ 2`, from the input `[w, k]` (`W = Fin w`):
1. the expected bit cost is at most `C(w + |k| + 2)^K`, and on every halting tape the output
   decodes (`decodeHash`) to a pair `F` with `B ≤ C k / log₂ k`, `q₂ ≤ C log₂² k`,
   `t ≤ C log₂ k`;
2. for every `T ⊆ W` with `|T| ≤ k`, the event "the run halts and its output separates `T`"
   is measurable and has probability at least `3/4`.

**Formalization Note** `k` is the parameter of the preprocessed instance, so `k ≥ 2`
(Section 2.1); `k / log k` is undefined at `k = 1`. The output format of `F` is fixed by
`decodeHash`. -/
theorem lemma_4_2 :
    ∃ (P : TimeSpaceMA.Program) (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ (w k : ℕ), 2 ≤ k →
        SoftmaxAttnFD.LasVegasWithin P (TimeSpaceMA.memOf [w, k])
          (fun mem => ∃ F : TwoLevelHash (Fin w), decodeHash w (outputList mem) = some F ∧
            (F.B : ℝ) ≤ C * k / Real.logb 2 k ∧ (F.q2 : ℝ) ≤ C * Real.logb 2 k ^ 2 ∧
            (F.t : ℝ) ≤ C * Real.logb 2 k)
          (C * ((w : ℝ) + bitLen [k] + 2) ^ K) ∧
        ∀ T : Finset (Fin w), T.card ≤ k →
          MeasurableSet {τ : ℕ → Bool | SoftmaxAttnFD.cost P (TimeSpaceMA.memOf [w, k]) τ < ⊤ ∧
            ∃ F : TwoLevelHash (Fin w), decodeHash w (outputList
              (SoftmaxAttnFD.final P (TimeSpaceMA.memOf [w, k]) τ)) = some F ∧ Separates F T} ∧
          (3 / 4 : ℝ≥0∞) ≤ SoftmaxAttnFD.coinTape
            {τ : ℕ → Bool | SoftmaxAttnFD.cost P (TimeSpaceMA.memOf [w, k]) τ < ⊤ ∧
              ∃ F : TwoLevelHash (Fin w), decodeHash w (outputList
                (SoftmaxAttnFD.final P (TimeSpaceMA.memOf [w, k]) τ)) = some F ∧
                Separates F T} := by sorry

end HSElemKernel
