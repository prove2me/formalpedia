-- Prove2me | Theorems.Thm_HSElemKernel_lemma_2_1
-- name    : HSElemKernel.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:25:29.015189+00:00
-- url     : https://prove2.me/theorems/abea72aa-5d40-4f46-8849-ee3d1bb99b29
-- title:
--   Lemma 2.1 — a kernel with $O_d(k^{d-1})$ elements and $O_d(k^d)$ sets, $k$ not increased
-- statement:
--   Fix $d$. There is a deterministic polynomial-time algorithm that maps every instance $(U, \mathcal S, k)$ of $d$-Hitting Set to an equivalent instance $(U', \mathcal S', k')$ of $d$-Hitting Set with
--   $$|U'| = O_d(k^{d-1}), \qquad |\mathcal S'| = O_d(k^d), \qquad k' \le k .$$
--
--   Precisely: there are a coin-free program $P$ and constants $C > 0$ and $K$, depending only on $d$, such that for every instance $I$ of $d$-Hitting Set and every code $c$ of $I$, the run of $P$ on $c$ halts within bit cost $C(|c| + 2)^K$ and outputs an instance $I'$ of $d$-Hitting Set with $|U'| \le C(k+2)^{d-1}$, $|\mathcal S'| \le C(k+2)^d$, $k' \le k$, which is a YES-instance if and only if $I$ is.
--
--   This known kernel (Abu-Khzam; van Bevern; Liu–Xiao) is Step 1 of the paper's kernelization: it bounds the universe and the number of sets polynomially in $k$ before the re-encoding.
--
--   **Formalization Note** The paper names no machine model. Running times are measured on the published logarithmic-cost RAM with fair coins (`TimeSpaceMA_RAM`, with the cost layer `SoftmaxAttnFD_Machine`): every executed instruction costs one plus the bit lengths of the addresses and values it touches. Inputs are lists of natural numbers placed in memory from cell $0$; outputs are read from memory (cell $0$ holds the output length) through a fixed strict decoder. At $d = 0$ the exponent $d - 1$ is truncated to $0$; the statement stays true there.
--
--   Differences from the source:
--   - encoding: polynomial-time algorithm on an unnamed machine → program of the published log-cost RAM TimeSpaceMA_RAM with cost layer SoftmaxAttnFD_Machine; bit cost bounded by C(|c|+2)^K in the input bit length |c|; reason: (expected) polynomial time is the same class on polynomially equivalent machine models
--   - encoding: O_d(f(k)) → C·f(k+2) with C (and P, K) chosen after d and before the instance; reason: covers k = 0, where (k)^(d−1) and k^d vanish; within a constant factor of f(k) for k ≥ 1
--   - encoding: an instance (U, S, k) as input and output → U = Fin n, S a Finset of Finsets; input: every code of IsInstCode (any listing order); output read through the fixed strict decoder outputOf; reason: relabelling a finite universe changes no instance, and every presentation of the instance is covered
--   - reading: a kernel "without increasing the parameter k" → output d-Hitting Set instance I' equivalent to I with k' ≤ k and the two size bounds; reason: the definition of a kernel in Section 3.1 with the stated sizes
--   - reading: O_d(k^(d−1)) elements "for every fixed d" → C(k+2)^(d−1) with the natural-number exponent d − 1, which is 0 at d = 0; reason: at d = 0 the page's k^(−1) is not a meaningful element count (every set is ∅); for d ≥ 1, and for the paper's standing d ≥ 3, it is the page's bound
-- source:
--   Sheng–Xiao, A Near-Linear Element-Kernel for d-Hitting Set, arXiv:2609.06512 (held version, sha256 aca9c70e…), Lemma 2.1, p.3

import Mathlib
import Definitions.Def_SoftmaxAttnFD_Machine
import Definitions.Def_HSElemKernel_IsDHS
import Definitions.Def_HSElemKernel_IsYes
import Definitions.Def_HSElemKernel_IsInstCode
import Definitions.Def_HSElemKernel_outputOf
import Definitions.Def_HSElemKernel_bitLen

namespace HSElemKernel

/-- **Lemma 2.1** (Sheng–Xiao, *A Near-Linear Element-Kernel for d-Hitting Set*, arXiv:2609.06512 (held version, sha256 aca9c70e…), Lemma 2.1, p.3; cited from [AK10, vB14, LX27]): for every fixed `d`,
`d`-Hitting Set admits a kernel with `O_d(k^{d−1})` elements and `O_d(k^d)` sets, without
increasing the parameter `k`.

For every `d` there are a coin-free program `P` of the published log-cost RAM and constants
`C, K`, chosen before the instance, such that on every code `c` of every `d`-Hitting Set
instance `I`, `P` halts within bit cost `C(|c| + 2)^K` and outputs (through the fixed decoder
`outputOf`) a `d`-Hitting Set instance `I'` with `n' ≤ C(k + 2)^{d−1}`,
`|S'| ≤ C(k + 2)^d`, `k' ≤ k`, equivalent to `I`.

**Formalization Note** The paper names no machine: the published RAM `TimeSpaceMA_RAM` with the
cost layer `SoftmaxAttnFD_Machine`. `O_d(f(k))` is `C·f(k + 2)` with `C` chosen after `d`
and before the instance. At `d = 0` the truncated exponent `d − 1 = 0` gives the bound `C`,
which is true (the only possible set is `∅`). -/
theorem lemma_2_1 (d : ℕ) :
    ∃ (P : TimeSpaceMA.Program) (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ I : HSInstance, IsDHS d I → ∀ c : List ℕ, IsInstCode I c →
        SoftmaxAttnFD.DeterministicWithin P (TimeSpaceMA.memOf c)
          (fun mem => ∃ I' : HSInstance, outputOf mem = some I' ∧ IsDHS d I' ∧
            (I'.n : ℝ) ≤ C * ((I.k : ℝ) + 2) ^ (d - 1) ∧
            (I'.S.card : ℝ) ≤ C * ((I.k : ℝ) + 2) ^ d ∧
            I'.k ≤ I.k ∧ (IsYes I ↔ IsYes I'))
          (C * ((bitLen c : ℝ) + 2) ^ K) := by sorry

end HSElemKernel
