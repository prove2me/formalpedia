-- Prove2me | Theorems.Thm_HSElemKernel_Supplement_theorem_1_2
-- name    : HSElemKernel.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T15:01:26.413931+00:00
-- url     : https://prove2.me/theorems/d6f4b6e1-3a4d-4dee-97a9-016d59a23ed2
-- title:
--   Theorem 1.2 — a deterministic kernel with $O_d(k^{7/4}\log^{3/2} k)$ elements, $O_d(k^{d+3/2}\log k)$ sets and $k' = O_d(k^{7/4}\log^{3/2} k)$
-- statement:
--   Fix $d \ge 3$. There is a deterministic polynomial-time algorithm that maps every instance $(U, \mathcal S, k)$ of $d$-Hitting Set to an equivalent instance $(U', \mathcal S', k')$ of $d$-Hitting Set with
--   $$
--   |U'| = O_d\big(k^{7/4}\log^{3/2} k\big), \qquad |\mathcal S'| = O_d\big(k^{d+3/2}\log k\big), \qquad k' = O_d\big(k^{7/4}\log^{3/2} k\big).
--   $$
--
--   Precisely: there are a coin-free program $P$ and constants $C > 0$ and $K$, depending only on $d$, such that for every instance $I = (U, \mathcal S, k)$ of $d$-Hitting Set and every code $c$ of $I$, every run of $P$ on $c$ halts within bit cost $C(|c| + 2)^K$ and outputs an instance $I' = (U', \mathcal S', k')$ of $d$-Hitting Set with
--   1. $|U'| \le C\,(k+2)^{7/4}\,\log_2^{3/2}(k+2)$,
--   2. $|\mathcal S'| \le C\,(k+2)^{d+3/2}\,\log_2(k+2)$,
--   3. $k' \le C\,(k+2)^{7/4}\,\log_2^{3/2}(k+2)$,
--   4. $I'$ is a YES-instance if and only if $I$ is.
--
--   This is the deterministic companion of the paper's randomized near-linear element kernel (Theorem 1.1). For $d = 3$ its element bound $O(k^{7/4}\log^{3/2} k)$ is below the quadratic element bound of the known kernels, without any error probability.
--
--   **Formalization Note** The paper names no machine model. Running times are measured on the published logarithmic-cost RAM (`TimeSpaceMA_RAM`, with the cost layer `SoftmaxAttnFD_Machine`); a deterministic algorithm is a coin-free program whose cost bound and output property hold on every run. Instances are $(\mathrm{Fin}\,n, \mathcal S, k)$, read from any code of the instance and written through a fixed strict decoder. The fractional exponents are real powers of the positive numbers $k+2$ and $\log_2(k+2) \ge 1$.
--
--   Differences from the source:
--   - encoding: polynomial-time algorithm on an unnamed machine → coin-free program of the published log-cost RAM TimeSpaceMA_RAM with cost layer SoftmaxAttnFD_Machine (DeterministicWithin); bit cost bounded by C(|c|+2)^K in the input bit length |c|; reason: polynomial time is the same class on polynomially equivalent machine models
--   - encoding: O_d(f(k)) → C·f(k+2) with C (and P, K) chosen after d and before the instance; reason: covers k = 0, 1, where k^{7/4}·log^{3/2} k and k^{d+3/2}·log k vanish; within a constant factor of f(k) for k ≥ 2
--   - encoding: an instance (U, S, k) as input and output → U = Fin n, S a Finset of Finsets; input: every code of IsInstCode (any listing order); output read through the fixed strict decoder outputOf; reason: relabelling a finite universe changes no instance, and every presentation of the instance is covered
--   - reading: "deterministic kernel" with the stated sizes → output d-Hitting Set instance I' with IsYes I ↔ IsYes I' and the three size bounds (elements, sets, k′); reason: the definition of a kernel in Section 3.1 (output of the same problem, equivalent, size bounded in k)
-- source:
--   Sheng–Xiao, A Near-Linear Element-Kernel for d-Hitting Set, arXiv:2609.06512 (held version, sha256 aca9c70e…), Theorem 1.2, p.2 (proof in Section 2.4, p.6, via Lemma 2.3, p.5 / Section 5, and Lemma 2.4, p.5)

import Mathlib
import Definitions.Def_SoftmaxAttnFD_Machine
import Definitions.Def_HSElemKernel_IsDHS
import Definitions.Def_HSElemKernel_IsYes
import Definitions.Def_HSElemKernel_IsInstCode
import Definitions.Def_HSElemKernel_outputOf
import Definitions.Def_HSElemKernel_bitLen

namespace HSElemKernel.Supplement

/-- **Theorem 1.2** (Sheng–Xiao, *A Near-Linear Element-Kernel for d-Hitting Set*, arXiv:2609.06512
(held version, sha256 aca9c70e…), Theorem 1.2, p.2; proof in §2.4, p.6, via Lemma 2.3 (§5) and
Lemma 2.4): for every fixed `d ≥ 3`, `d`-Hitting Set admits a deterministic kernel with
`O_d(k^{7/4} log^{3/2} k)` elements, `O_d(k^{d+3/2} log k)` sets, and output parameter
`k' = O_d(k^{7/4} log^{3/2} k)`.

For every `d ≥ 3` there are a coin-free program `P` of the published log-cost RAM and constants
`C > 0, K`, chosen after `d` and before the instance, such that on every code `c` of every
`d`-Hitting Set instance `I`, every run of `P` halts within bit cost `C(|c| + 2)^K` and outputs
(through the fixed decoder `outputOf`) a `d`-Hitting Set instance `I'` with
`n' ≤ C(k+2)^{7/4} log₂^{3/2}(k+2)`, `|S'| ≤ C(k+2)^{d+3/2} log₂(k+2)`,
`k' ≤ C(k+2)^{7/4} log₂^{3/2}(k+2)`, and `I` is a YES-instance iff `I'` is.

**Formalization Note** The paper names no machine: the published RAM `TimeSpaceMA_RAM` with the
cost layer `SoftmaxAttnFD_Machine` (`DeterministicWithin`: coin-free, and on every tape the cost
bound and the output property hold). `O_d(f(k))` is `C·f(k + 2)` with `C` chosen after `d` and
before the instance (`log k` vanishes at `k = 1`); the fractional exponents are real powers
(`Real.rpow`) of positive bases (`log₂(k + 2) ≥ 1`). Instances are `(Fin n, S, k)`, read from any
code (`IsInstCode`) and written through the fixed strict decoder `outputOf`. -/
theorem theorem_1_2 (d : ℕ) (hd : 3 ≤ d) :
    ∃ (P : TimeSpaceMA.Program) (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ I : HSInstance, IsDHS d I → ∀ c : List ℕ, IsInstCode I c →
        SoftmaxAttnFD.DeterministicWithin P (TimeSpaceMA.memOf c)
          (fun mem => ∃ I' : HSInstance, outputOf mem = some I' ∧ IsDHS d I' ∧
            (I'.n : ℝ) ≤
              C * ((I.k : ℝ) + 2) ^ (7 / 4 : ℝ) * Real.logb 2 ((I.k : ℝ) + 2) ^ (3 / 2 : ℝ) ∧
            (I'.S.card : ℝ) ≤
              C * ((I.k : ℝ) + 2) ^ ((d : ℝ) + 3 / 2) * Real.logb 2 ((I.k : ℝ) + 2) ∧
            (I'.k : ℝ) ≤
              C * ((I.k : ℝ) + 2) ^ (7 / 4 : ℝ) * Real.logb 2 ((I.k : ℝ) + 2) ^ (3 / 2 : ℝ) ∧
            (IsYes I ↔ IsYes I'))
          (C * ((bitLen c : ℝ) + 2) ^ K) := by sorry

end HSElemKernel.Supplement
