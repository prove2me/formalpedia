-- Prove2me | Theorems.Thm_HSElemKernel_lemma_2_4
-- name    : HSElemKernel.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:25:43.918197+00:00
-- url     : https://prove2.me/theorems/f2beef88-a80b-46bb-9c39-09a87f95bd0c
-- title:
--   Lemma 2.4 — variable-pair reduction from width-$d$ CNF to $d$-Hitting Set with $2N$ elements
-- statement:
--   Let $d \ge 3$ and let $\Psi$ be a CNF formula with $N$ variables and $M$ clauses, each of width at most $d$. In time linear in the encoding length of $\Psi$, one can construct an equivalent $d$-Hitting Set instance $(U', \mathcal S', k')$ with
--   $$|U'| = 2N, \qquad |\mathcal S'| \le N + M, \qquad k' = N .$$
--
--   Precisely: there are a coin-free program $P$ and a constant $C$ such that, on the code of every such $\Psi$, $P$ halts after at most $C(N + |\mathrm{code}(\Psi)| + 1)$ executed instructions, and its output is an instance $I'$ of $d$-Hitting Set with exactly $2N$ elements, at most $N + M$ sets and parameter $N$, which is a YES-instance if and only if $\Psi$ is satisfiable.
--
--   This is Step 3 of the kernelization: it turns the few variables of the encoding into few elements.
--
--   **Formalization Note** "Linear time" counts executed instructions of the published RAM (unit cost); the encoding length of $\Psi$ is the number of entries of its code plus $N$.
--
--   Differences from the source:
--   - encoding: "in time linear in the encoding length of Ψ" on an unnamed machine → coin-free program of the published RAM halting after at most C(N + |cnfCode Ψ| + 1) executed instructions; reason: unit-cost step count; a log-cost machine cannot read its input in linear bit cost
--   - reading: the encoding length of Ψ → the number of entries of cnfCode Ψ plus N; reason: a formula on N variables is written with its N variables, and the output already contains N pair sets, so no reduction runs in time o(N)
--   - encoding: Ψ and the output instance → Ψ a published MainResults.CNF N given by its code cnfCode Ψ; output read by the strict decoder outputOf; "equivalent" as Satisfiable Ψ ↔ IsYes I'; reason: representation of formulas and instances
-- source:
--   Sheng–Xiao, A Near-Linear Element-Kernel for d-Hitting Set, arXiv:2609.06512 (held version, sha256 aca9c70e…), Lemma 2.4, p.5

import Mathlib
import Definitions.Def_SoftmaxAttnFD_Machine
import Definitions.Def_MainResults
import Definitions.Def_HSElemKernel_IsDHS
import Definitions.Def_HSElemKernel_IsYes
import Definitions.Def_HSElemKernel_cnfCode
import Definitions.Def_HSElemKernel_outputOf
import Definitions.Def_HSElemKernel_haltSteps

namespace HSElemKernel

/-- **Lemma 2.4** (variable-pair reduction; Sheng–Xiao, *A Near-Linear Element-Kernel for d-Hitting Set*, arXiv:2609.06512 (held version, sha256 aca9c70e…), Lemma 2.4, p.5): let `Ψ` be a CNF formula
with `N` variables and `M` clauses, each of width at most `d`, where `d ≥ 3`. In time linear
in the encoding length of `Ψ`, one can construct an equivalent `d`-Hitting Set instance with
exactly `2N` elements, at most `N + M` sets, and parameter `N`.

For `d ≥ 3` there are a coin-free program `P` of the published RAM and a constant `C` such
that on the code of every such `Ψ`, `P` halts after at most `C(N + |code(Ψ)| + 1)` executed
instructions and outputs (`outputOf`) a `d`-Hitting Set instance `I'` with `n' = 2N`,
`|S'| ≤ N + M`, `k' = N`, which is a YES-instance iff `Ψ` is satisfiable.

**Formalization Note** "Linear time" counts executed instructions (`haltSteps`; unit cost),
since a log-cost machine cannot read its input in linear bit cost. The encoding length of `Ψ` is
the number of entries of `cnfCode Ψ` plus `N`: a formula on `N` variables is written with its
`N` variables, and the output already has `N` pair sets. -/
theorem lemma_2_4 (d : ℕ) (hd : 3 ≤ d) :
    ∃ (P : TimeSpaceMA.Program) (C : ℕ), P.CoinFree ∧
      ∀ (N : ℕ) (Ψ : MainResults.CNF N), (∀ cl ∈ Ψ, cl.length ≤ d) →
        (∃ T, (SoftmaxAttnFD.run P (TimeSpaceMA.memOf (cnfCode Ψ)) TimeSpaceMA.zeroTape T).halted
            = true) ∧
        haltSteps P (TimeSpaceMA.memOf (cnfCode Ψ)) TimeSpaceMA.zeroTape ≤
          C * (N + (cnfCode Ψ).length + 1) ∧
        ∃ I' : HSInstance,
          outputOf (SoftmaxAttnFD.final P (TimeSpaceMA.memOf (cnfCode Ψ)) TimeSpaceMA.zeroTape)
            = some I' ∧
          IsDHS d I' ∧ I'.n = 2 * N ∧ I'.S.card ≤ N + Ψ.length ∧ I'.k = N ∧
          (MainResults.Satisfiable Ψ ↔ IsYes I') := by sorry

end HSElemKernel
