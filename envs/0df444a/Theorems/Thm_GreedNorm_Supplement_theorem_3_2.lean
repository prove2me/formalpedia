-- Prove2me | Theorems.Thm_GreedNorm_Supplement_theorem_3_2
-- name    : GreedNorm.Supplement.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:52:33.350202+00:00
-- url     : https://prove2.me/theorems/6ffc8d39-c9d3-43f7-9f1b-205f10ee2a22
-- title:
--   Theorem 3.2 — an $\alpha$-approximation for BudgCard gives a $\frac{3(1+\epsilon)}{\alpha}\ln n$-approximation for SubaddNestedCostAlloc (corrected: $\max\{1,\cdot\}$)
-- statement:
--   **Nested Cost Allocation with monotone subadditive loads (SubaddNestedCostAlloc).** A universe $U$ of $n$ elements, $m\ge1$ parts, load functions $\mathrm{load}_i:2^U\to\mathbb R_{\ge0}$ that are monotone ($A\subseteq B\Rightarrow\mathrm{load}_i(A)\le\mathrm{load}_i(B)$) and subadditive ($\mathrm{load}_i(A\cup B)\le\mathrm{load}_i(A)+\mathrm{load}_i(B)$), and a monotone symmetric norm $g$ on $\mathbb R^m$. An assignment $\sigma:U\to[m]$ has load vector $\mathrm{load}(\sigma)=(\mathrm{load}_i(\sigma^{-1}(i)))_{i\in[m]}$ and cost $g(\mathrm{load}(\sigma))$; $\mathrm{OPT}$ is the least cost.
--
--   **Theorem.** Let $0<\alpha\le1$ and $\epsilon>0$. There is a deterministic polynomial-time algorithm that, given oracle access to the loads, to $g$ and to any $\alpha$-approximation algorithm for BudgCard, outputs an assignment $\sigma$ with
--
--   $$
--   g(\mathrm{load}(\sigma))\ \le\ \max\Big\{1,\ \frac{3(1+\epsilon)}{\alpha}\ln n\Big\}\cdot\mathrm{OPT}.
--   $$
--
--   Formally: one admissible program of the BudgCard-oracle real RAM, fixed from $\alpha$ and $\epsilon$ only, halts on every instance and with **every** $\alpha$-approximate BudgCard oracle within $C(n+m+2)^k$ steps (oracle calls cost one step), and its output cells hold such a $\sigma$.
--
--   This is the paper's general reduction: approximating the non-nested BudgCard problem suffices to approximate the nested problem, and with the exact NormBudgCard algorithm ($\alpha=1$) it gives Theorem 1.3.
--
--   **Formalization Note** $U=\{0,\dots,n-1\}$ and parts are $0$-based. Input: integer cells $0,1$ hold $n,m$; output: integer cell $2+j$ holds $\sigma(j)$. $\mathrm{OPT}$ is written as a bound against every assignment $\sigma'$. No normalization $\mathrm{load}_i(\emptyset)=0$ is assumed; $\ln$ is the natural logarithm.
--
--   Differences from the source:
--   - correction: ratio (3(1+ϵ)/α) ln n → ratio max{1, (3(1+ϵ)/α) ln n}; reason: at n = 1 the printed ratio is 0; counterexample n = m = 1, load_1({e}) = 1, load_1(∅) = 0, g = |·|, OPT = 1, and every assignment costs 1 > 0; for n ≥ 2 the two agree since 3 ln 2/α > 1
--   - encoding: an α-approximation algorithm for BudgCard implies an approximation algorithm → one admissible BudgMachine program, chosen from α and ϵ before the instance, that works with every oracle satisfying IsAlphaBudgOracle α, unit-cost oracle calls, halting within C(n+m+2)^k steps; reason: standard oracle-reduction reading of "implies"; loads and g have no finite description and are value oracles
--   - encoding: OPT (minimum cost) → a bound against the cost of every total assignment σ'; reason: equivalent: the ratio is positive and OPT is the minimum over finitely many assignments
--   - encoding: m load functions (m parts), universe U of n elements → 0 < m, universe Fin n, parts Fin m; reason: with m = 0 and n ≥ 1 no assignment exists; 0-based indexing changes no instance
--   - reading: an assignment σ (Definition 1.2, which also defines cov(σ) for assignments that leave elements unassigned) → total assignments σ : Fin n → Fin m, both for the output and for OPT; reason: minimizing over partial assignments is trivial (by monotonicity the empty assignment is optimal), and the paper's own use fixes total ones (Lemma 3.5: OPT is attained by "an assignment σ* that assigns all n elements"; §3.1 aggregation: "σ assigns every element")
--   - encoding: an α-approximation algorithm (α unrestricted in the statement) → 0 < α ≤ 1; reason: BudgCard is a maximization problem, so an α-approximation has α ≤ 1 (for α > 1 none exists on any instance with a nonempty feasible set), and the proof of Lemma 3.5 uses the remaining fraction 1 − α ≥ 0
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), Theorem 3.2, p.6 (PDF 8); Definition 1.2, p.2 (PDF 4); Definition 3.1, p.6 (PDF 8)

import Mathlib
import Definitions.Def_SymNormLoad_IsMonotoneSymmetricNorm
import Definitions.Def_SubmodOrder_Subadditive
import Definitions.Def_SubsamplingSM_Offline_IsMonotoneSetFn
import Definitions.Def_GreedNorm_partialLoadVec
import Definitions.Def_GreedNorm_Machine
import Definitions.Def_GreedNorm_Supplement_BudgMachine
import Definitions.Def_GreedNorm_Supplement_IsAlphaBudgOracle

namespace GreedNorm.Supplement

/-- **Theorem 3.2: an `α`-approximation for BudgCard gives a `(3(1+ϵ)/α) ln n`-approximation for
SubaddNestedCostAlloc** (corrected: ratio `max{1, (3(1+ϵ)/α) ln n}`).
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256
2a3d250c…a300b1b6), Theorem 3.2, p.6 (PDF 8): "An α-approximation algorithm for BudgCard implies a
(3(1+ϵ)/α · ln n)-approximation algorithm for SubaddNestedCostAlloc for every ϵ > 0", with
Definition 1.2, p.2 (PDF 4), and Definition 3.1, p.6 (PDF 8).

For every `0 < α ≤ 1` and `ϵ > 0` there are one admissible program `P` of the BudgCard-oracle
real RAM and constants `C, k` such that for every instance of Nested Cost Allocation with
monotone subadditive loads (universe `Fin n`, `m ≥ 1` parts, load functions
`load_i : 2^U → ℝ_{≥0}` that are monotone and subadditive, a monotone symmetric norm `g`) and
for **every** `α`-approximate BudgCard oracle `budg`, the run of `P` halts within
`C (n + m + 2)^k` steps with a total assignment `σ` such that
`g(load(σ)) ≤ max{1, (3(1+ϵ)/α) ln n} · g(load(σ'))` for every total assignment `σ'`, i.e.
`≤ max{1, (3(1+ϵ)/α) ln n} · OPT`.

**Formalization Note** Input: integer cells `0, 1` hold `n, m`; all other memory is `0`; the
loads, `g` and the BudgCard algorithm are reachable only through the oracle instructions, each
call one step. Output: on halting, integer cell `2 + j` holds `σ(j)`. The cost of a total
assignment `σ` is `g(partialLoadVec load (some ∘ σ))`, Definition 1.2's `g(load(σ))`; OPT is
the minimum over the `m^n` total assignments, written as a bound against each of them. No
`load_i(∅) = 0` is assumed. `ln` is `Real.log`. The program may depend on `α` and `ϵ`, never
on the instance or the oracle. At `n = 1` the printed ratio `0` is false, hence `max{1, ·}`. -/
theorem theorem_3_2 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : Supplement.BudgMachine.Program, Supplement.BudgMachine.Admissible P ∧ ∃ C k : ℕ,
      ∀ (n m : ℕ), 0 < m →
      ∀ (load : Fin m → Finset (Fin n) → ℝ), (∀ i S, 0 ≤ load i S) →
        (∀ i, SubsamplingSM.Offline.IsMonotoneSetFn (load i)) →
        (∀ i, SubmodOrder.Subadditive (load i)) →
      ∀ (g : (Fin m → ℝ) → ℝ), SymNormLoad.IsMonotoneSymmetricNorm g →
      ∀ (budg : Fin m → Finset (Fin n) → ℝ → Finset (Fin n)),
        Supplement.IsAlphaBudgOracle α load budg →
        let s₀ : Machine.State := Machine.init (fun _ => 0)
          (fun a => if a = 0 then (n : ℤ) else if a = 1 then (m : ℤ) else 0)
        ∃ t : ℕ, t ≤ C * (n + m + 2) ^ k ∧
          (Supplement.BudgMachine.run P load g budg s₀ t).halted = true ∧
          ∃ σ : Fin n → Fin m,
            (∀ j : Fin n, (Supplement.BudgMachine.run P load g budg s₀ t).integerMemory
              (2 + (j : ℤ)) = ((σ j : ℕ) : ℤ)) ∧
            ∀ σ' : Fin n → Fin m,
              g (partialLoadVec load (fun e => some (σ e))) ≤
                max 1 (3 * (1 + ε) / α * Real.log (n : ℝ)) *
                  g (partialLoadVec load (fun e => some (σ' e))) := by sorry

end GreedNorm.Supplement
