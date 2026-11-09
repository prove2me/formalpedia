-- Prove2me | Theorems.Thm_HSElemKernel_theorem_1_1
-- name    : HSElemKernel.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:25:53.670885+00:00
-- url     : https://prove2.me/theorems/009453a7-eb95-42ac-8aed-46fc7c911c1d
-- title:
--   Theorem 1.1 — a one-sided randomized kernel with $O_d(k\log^3 k)$ elements and $O_d(k^d\log^{2d-2} k)$ sets
-- statement:
--   For every fixed $d \ge 3$, $d$-Hitting Set admits a one-sided randomized kernel computable in expected polynomial time with success probability at least $3/4$. The output has $O_d(k\log^3 k)$ elements, $O_d(k^d\log^{2d-2} k)$ sets, and parameter $k' = O_d(k\log^3 k)$.
--
--   Precisely: for every $d \ge 3$ there are a program $P$ with fair coins and constants $C > 0$, $K$, chosen before the instance, such that for every instance $I = (U, \mathcal S, k)$ of $d$-Hitting Set and every code $c$ of $I$:
--
--   1. the expected bit cost of the run on $c$ is at most $C(|c| + 2)^K$, and on every coin sequence on which the run halts, the output is an instance $I' = (U', \mathcal S', k')$ of $d$-Hitting Set with
--   $$|U'| \le C(k+2)\log_2^3(k+2), \qquad |\mathcal S'| \le C(k+2)^d\log_2^{2d-2}(k+2), \qquad k' \le C(k+2)\log_2^3(k+2),$$
--   and $I'$ is a NO-instance whenever $I$ is;
--   2. if $I$ is a YES-instance, the event that the run halts and outputs a YES-instance is measurable and has probability at least $3/4$.
--
--   The theorem answers affirmatively, with randomization, the question whether the $O(k^{d-1})$ element bound for $d$-Hitting Set kernels can be improved by a polynomial factor: the number of elements becomes near-linear in $k$ for every fixed $d$.
--
--   **Formalization Note** The paper names no machine model. Running times are measured on the published logarithmic-cost RAM with fair coins (`TimeSpaceMA_RAM`, with the cost layer `SoftmaxAttnFD_Machine`): every executed instruction costs one plus the bit lengths of the addresses and values it touches. Inputs are lists of natural numbers placed in memory from cell $0$; outputs are read from memory (cell $0$ holds the output length) through a fixed strict decoder. A finite expected cost forces halting with probability one.
--
--   Differences from the source:
--   - encoding: polynomial-time algorithm on an unnamed machine → program of the published log-cost RAM TimeSpaceMA_RAM with cost layer SoftmaxAttnFD_Machine; bit cost bounded by C(|c|+2)^K in the input bit length |c|; reason: (expected) polynomial time is the same class on polynomially equivalent machine models
--   - encoding: O_d(f(k)) → C·f(k+2) with C (and P, K) chosen after d and before the instance; reason: covers k = 0, 1, where k log³ k vanishes; within a constant factor of f(k) for k ≥ 2
--   - encoding: an instance (U, S, k) as input and output → U = Fin n, S a Finset of Finsets; input: every code of IsInstCode (any listing order); output read through the fixed strict decoder outputOf; reason: relabelling a finite universe changes no instance, and every presentation of the instance is covered
--   - reading: kernel output size "|I′| + k′ ≤ f(k)" with O_d(k log³ k) elements, O_d(k^d log^(2d−2) k) sets and k′ = O_d(k log³ k) → IsDHS d I' and the three explicit bounds on |U′|, |S′| and k′; reason: with sets of size at most d these bound |I′| + k′ by a computable function of k and give the stated counts
--   - encoding: "never maps a NO-instance to a YES-instance"; success probability at least 3/4 → on every halting coin sequence; the coin-tape measure of the measurable event {halts and outputs a YES-instance} is ≥ 3/4; reason: the expected-cost bound forces halting with probability one
-- source:
--   Sheng–Xiao, A Near-Linear Element-Kernel for d-Hitting Set, arXiv:2609.06512 (held version, sha256 aca9c70e…), Theorem 1.1, p.2

import Mathlib
import Definitions.Def_SoftmaxAttnFD_Machine
import Definitions.Def_HSElemKernel_IsDHS
import Definitions.Def_HSElemKernel_IsYes
import Definitions.Def_HSElemKernel_IsInstCode
import Definitions.Def_HSElemKernel_outputOf
import Definitions.Def_HSElemKernel_bitLen

open MeasureTheory
open scoped ENNReal

namespace HSElemKernel

/-- **Theorem 1.1** (Sheng–Xiao, *A Near-Linear Element-Kernel for d-Hitting Set*, arXiv:2609.06512 (held version, sha256 aca9c70e…), Theorem 1.1, p.2): for every fixed `d ≥ 3`, `d`-Hitting Set admits a
one-sided randomized kernel computable in expected polynomial time with success probability at
least `3/4`. The output has `O_d(k log³ k)` elements, `O_d(k^d log^{2d−2} k)` sets, and parameter
`k' = O_d(k log³ k)`.

For every `d ≥ 3` there are a program `P` of the published log-cost RAM with fair coins and
constants `C, K`, chosen before the instance, such that for every `d`-Hitting Set instance `I`
and every code `c` of it:
1. the expected bit cost is at most `C(|c| + 2)^K`, and on every tape on which the run halts
   the output decodes (`outputOf`) to a `d`-Hitting Set instance `I'` with
   `n' ≤ C(k + 2) log₂³(k + 2)`, `|S'| ≤ C(k + 2)^d log₂^{2d−2}(k + 2)`,
   `k' ≤ C(k + 2) log₂³(k + 2)`, and `I'` is a NO-instance whenever `I` is;
2. if `I` is a YES-instance, the event "the run halts and outputs a YES-instance" is measurable
   and has probability at least `3/4`.

**Formalization Note** The paper names no machine: the published RAM `TimeSpaceMA_RAM` with fair
coins and its expected-cost layer `SoftmaxAttnFD_Machine` (`LasVegasWithin`; a finite expected
cost forces halting with probability one). `O_d(f(k))` is `C·f(k + 2)` with `C` chosen after
`d` and before the instance (`k log³ k` vanishes at `k = 0, 1`). Instances are `(Fin n, S, k)`,
read from any code (`IsInstCode`) and written through the fixed strict decoder `outputOf`. -/
theorem theorem_1_1 (d : ℕ) (hd : 3 ≤ d) :
    ∃ (P : TimeSpaceMA.Program) (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ I : HSInstance, IsDHS d I → ∀ c : List ℕ, IsInstCode I c →
        SoftmaxAttnFD.LasVegasWithin P (TimeSpaceMA.memOf c)
          (fun mem => ∃ I' : HSInstance, outputOf mem = some I' ∧ IsDHS d I' ∧
            (I'.n : ℝ) ≤ C * ((I.k : ℝ) + 2) * Real.logb 2 ((I.k : ℝ) + 2) ^ 3 ∧
            (I'.S.card : ℝ) ≤
              C * ((I.k : ℝ) + 2) ^ d * Real.logb 2 ((I.k : ℝ) + 2) ^ (2 * d - 2) ∧
            (I'.k : ℝ) ≤ C * ((I.k : ℝ) + 2) * Real.logb 2 ((I.k : ℝ) + 2) ^ 3 ∧
            (¬ IsYes I → ¬ IsYes I'))
          (C * ((bitLen c : ℝ) + 2) ^ K) ∧
        (IsYes I →
          MeasurableSet {τ : ℕ → Bool | SoftmaxAttnFD.cost P (TimeSpaceMA.memOf c) τ < ⊤ ∧
            ∃ I' : HSInstance,
              outputOf (SoftmaxAttnFD.final P (TimeSpaceMA.memOf c) τ) = some I' ∧ IsYes I'} ∧
          (3 / 4 : ℝ≥0∞) ≤ SoftmaxAttnFD.coinTape
            {τ : ℕ → Bool | SoftmaxAttnFD.cost P (TimeSpaceMA.memOf c) τ < ⊤ ∧
              ∃ I' : HSInstance,
                outputOf (SoftmaxAttnFD.final P (TimeSpaceMA.memOf c) τ) = some I' ∧
                IsYes I'}) := by sorry

end HSElemKernel
