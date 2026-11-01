-- Prove2me | Theorems.Thm_MinSharing_lemma_2_2
-- name    : MinSharing.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:25:46.051983+00:00
-- url     : https://prove2.me/theorems/e89c7ec2-ba91-4170-a654-199faf1ecf6a
-- title:
--   Lemma 2.2 — fPO of a given allocation is decidable with $O(nm(n+m))$ operations
-- statement:
--   There are a program $R$ of the real RAM and a constant $K>0$ such that, for all $n,m\ge1$, every $n\times m$ valuation matrix $v$ and every allocation $z$, the program started on the memory holding $n$, $m$, $v$ and $z$ halts within
--   $$K\cdot n\,m\,(n+m)$$
--   steps and accepts if and only if $z$ is fractionally Pareto-optimal for $v$.
--
--   The test is strongly polynomial: its number of operations depends on $n$ and $m$ only. It is the filter that removes non-fPO candidate graphs in the enumeration of Lemma 3.9.
--
--   Differences from the source:
--   - reading: decide in time O(nm(n+m)) → number of executed instructions of one program of the published real RAM (SmaleNinth.RAMProgram, unit cost, exact real arithmetic) bounded by K times the expression, with the output correct; reason: the paper counts arithmetic operations and comparisons on real numbers (multiplicative Bellman–Ford, App. A p.31; constant-size LPs, p.14)
--   - encoding: O(nm(n+m)) for all n, m → n, m ≥ 1 with R and K chosen before n and m; reason: the expression is 0 when n or m is 0, so the O-bound is about positive sizes; R reads n and m from its input
--   - encoding: z is an allocation → hypothesis IsFeasible z (z ≥ 0, every column sums to 1); reason: the definition of an allocation on p.7
--   - encoding: agents [n] = {1,…,n}, objects [m] = {1,…,m} → Fin n, Fin m (paper index = Lean index + 1); reason: Lean convention; same instances
-- source:
--   Sandomirskiy, Segal-Halevi, Efficient Fair Division with Minimal Sharing, arXiv:1908.01669v3, Lemma 2.2, p.9 (proof Appendix A, p.31)

import Mathlib
import Definitions.Def_CompetitiveChores_RichFamily_Setting
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_MinSharing_RAMInterface

set_option autoImplicit false

namespace MinSharing

open CompetitiveChores.RichFamily SmaleNinth

/-- **Lemma 2.2** (Sandomirskiy, Segal-Halevi, arXiv:1908.01669v3, p.9; proof Appendix A,
p.31). It is possible to decide in time `O(nm(n+m))` whether a given allocation `z` is
fractionally Pareto-optimal.

**Formalization Note** Time is the number of executed instructions of a program `R` of the
published real RAM (`SmaleNinth.RAMProgram`, unit cost, exact real arithmetic). One program `R`
and one constant `K > 0`, both chosen before `n` and `m`, work for all `n, m ≥ 1`. The input memory
`pairMem v z` holds `n`, `m`, the values `vᵢ,ₒ` and the shares `zᵢ,ₒ`; `R` halts within
`K·n·m·(n+m)` steps, accepting iff `z` is fPO. "A given allocation" is the hypothesis
`IsFeasible z`. -/
theorem lemma_2_2 :
    ∃ R : RAMProgram, ∃ K : ℝ, 0 < K ∧
      ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → ∀ v z : Fin n → Fin m → ℝ, IsFeasible z →
        DecidesWithin R (pairMem v z) (K * n * m * (n + m)) (IsParetoOptimal v z) := by sorry

end MinSharing
