-- Prove2me | Theorems.Thm_HSElemKernel_lemma_3_2
-- name    : HSElemKernel.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:26:30.224795+00:00
-- url     : https://prove2.me/theorems/12026ae5-7825-4b55-a595-7a68fb36ba07
-- title:
--   Lemma 3.2 — linear-size CNF encoding of $\sum_i x_i \bowtie b$
-- statement:
--   Let $x_1, \dots, x_N$ be Boolean variables, $b$ a nonnegative integer and $\bowtie \in \{=, \le\}$. The constraint
--   $$\sum_{i=1}^{N} x_i \bowtie b$$
--   can be encoded in polynomial time by a CNF formula such that an assignment of $x_1, \dots, x_N$ extends to a satisfying assignment of the formula if and only if it satisfies the constraint. The encoding has $O(N)$ auxiliary variables and $O(N)$ clauses, each of width at most three.
--
--   Precisely: there are a cardinality encoder $E$ and a constant $C$ such that $E$ meets this guarantee with constant $C$ for all $N$, $b$, $\bowtie$, and a coin-free program $P$ with exponent $K$ that, from the input $[N, b, \mathrm{code}(\bowtie)]$, halts within bit cost $C(N + |b| + 2)^K$ and outputs the code of $E$'s formula, with the constrained variables numbered first.
--
--   The encoding is used for the two cardinality requirements (5) and (6) of $\Phi_{\mathcal F}$.
--
--   **Formalization Note** The paper names no machine model. Running times are measured on the published logarithmic-cost RAM with fair coins (`TimeSpaceMA_RAM`, with the cost layer `SoftmaxAttnFD_Machine`): every executed instruction costs one plus the bit lengths of the addresses and values it touches. Inputs are lists of natural numbers placed in memory from cell $0$; outputs are read from memory (cell $0$ holds the output length) through a fixed strict decoder.
--
--   Differences from the source:
--   - encoding: O(N) auxiliary variables and clauses → ≤ C(N+1), one constant C for both and for the running time; reason: at N = 0 and b > 0 a clause is still needed; O(N) means a constant factor
--   - encoding: computable in polynomial time on an unnamed machine → coin-free program of the published log-cost RAM, input [N, b, code(▷◁)], bit cost ≤ C(N + |b| + 2)^K, output cnfCode of the formula; reason: the input consists of N variables and the number b; polynomially equivalent machine models give the same class
--   - encoding: variables x₁, …, x_N and fresh auxiliaries → variable type Fin N ⊕ Fin a; output numbers x_i as i and auxiliaries after them; reason: naming of variables
-- source:
--   Sheng–Xiao, A Near-Linear Element-Kernel for d-Hitting Set, arXiv:2609.06512 (held version, sha256 aca9c70e…), Lemma 3.2, p.7

import Mathlib
import Definitions.Def_SoftmaxAttnFD_Machine
import Definitions.Def_HSElemKernel_CardEncoder
import Definitions.Def_HSElemKernel_cnfCode
import Definitions.Def_HSElemKernel_outputList
import Definitions.Def_HSElemKernel_bitLen

namespace HSElemKernel

/-- **Lemma 3.2** (linear-size cardinality encoding; Sheng–Xiao, *A Near-Linear Element-Kernel for d-Hitting Set*, arXiv:2609.06512 (held version, sha256 aca9c70e…), Lemma 3.2, p.7): the constraint
`x₁ + ⋯ + x_N ▷◁ b` (`▷◁ ∈ {=, ≤}`, `b ≥ 0`) can be encoded in polynomial time by a CNF
formula such that an assignment of `x₁, …, x_N` extends to a satisfying assignment iff it
satisfies the constraint, with `O(N)` auxiliary variables and `O(N)` clauses, each of width at
most three.

There are an encoder `E` and a constant `C` meeting this guarantee at every `N, b, ▷◁`
(`E.Spec C`), and a coin-free program `P` with exponent `K` that, from the input
`[N, b, code(▷◁)]`, halts within bit cost `C(N + |b| + 2)^K` with the code of `E`'s formula
as output (the `N` constrained variables numbered `0, …, N−1`, the auxiliary ones after them).

**Formalization Note** `O(N)` is `C(N + 1)` (at `N = 0` with `b > 0` one clause is needed).
The running time is polynomial in `N` and the bit length of `b`. -/
theorem lemma_3_2 :
    ∃ (E : CardEncoder) (C : ℕ), E.Spec C ∧
      ∃ (P : TimeSpaceMA.Program) (K : ℕ), ∀ (N b : ℕ) (op : CardOp),
        SoftmaxAttnFD.DeterministicWithin P (TimeSpaceMA.memOf [N, b, op.code])
          (fun mem => outputList mem =
            cnfCode ((E.enc N b op).map (List.map fun l => (finSumFinEquiv l.1, l.2))))
          ((C : ℝ) * ((N : ℝ) + bitLen [b] + 2) ^ K) := by sorry

end HSElemKernel
