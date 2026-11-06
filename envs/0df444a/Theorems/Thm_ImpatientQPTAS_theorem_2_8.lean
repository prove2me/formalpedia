-- Prove2me | Theorems.Thm_ImpatientQPTAS_theorem_2_8
-- name    : ImpatientQPTAS.theorem_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:00:41.018313+00:00
-- url     : https://prove2.me/theorems/af4b63a2-693d-4690-8e82-889cd0285359
-- title:
--   Theorem 2.8 and §2.6 — the dynamic program is exact, in time $O(n^{O(|\Psi|\cdot|\Lambda|)})$
-- statement:
--   There is a universal constant $c$ such that the following holds for all $n$ customers grouped into $K$ nonempty classes, class $k$ having reward $\mathrm{rew}_k$ and departure probability $\mathrm{prob}_k\in[0,1]$:
--
--   1. the program `dp` uses at most $c\,(n+1)^{cK}$ operations;
--   2. its table holds the optimal value of every set $A$ at the count vector of $A$;
--   3. the greedy policy reading its action table is an adaptive service policy attaining that value from every start set.
--
--   Since $K\le|\Psi|\cdot|\Lambda|$, this with the counts of §§2.2–2.3 gives the printed $O(n^{O_\epsilon(\log^2 n)})$ time for an optimal policy of the rounded-up process.
--
--   Differences from the source:
--   - generalization: rewards and probabilities of the rounded-up process, in |Ψ|·|Λ| classes → any K nonempty classes with probabilities in [0, 1]; reason: the rounded-up process is the special case; K ≤ |Ψ|·|Λ|
--   - encoding: O(n^{O(|Ψ|·|Λ|)}) time → at most c·(n+1)^(c·K) counted operations, c universal; reason: (n+1) keeps the bound meaningful at n = 1; time is counted in Work
--   - encoding: states (t, N_t) → states N; reason: the value does not depend on the stage
-- source:
--   Segev, Near-Optimal Adaptive Policies for Serving Stochastically Departing Customers, arXiv:2209.13878v1, Theorem 2.8, p.12; §2.6, pp.13–14

import Mathlib
import Definitions.Def_CapacitatedAssort_General_Work
import Definitions.Def_ImpatientQPTAS_Model
import Definitions.Def_ImpatientQPTAS_Program

namespace ImpatientQPTAS

open CapacitatedAssort.General in
/-- Segev, arXiv:2209.13878v1, Theorem 2.8, p.12, in the form of §2.6, pp.13–14: "one can compute an
optimal service policy in O(n^{O(|Ψ|·|Λ|)}) time by means of dynamic programming".

Given `n` customers in `K` nonempty classes `cl`, class `k` having reward `rew k` and departure
probability `prob k ∈ [0, 1]`: the program `dp` uses at most `c·(n+1)^(c·K)` operations, its table holds
the optimal value of every set, and the greedy policy reading its action table is an adaptive service
policy attaining that value from every start set.

**Formalization Note.** `c` is universal. `K ≤ |Ψ|·|Λ|`, so with `distinct_values` this gives the printed
`O(n^{O_ε(log² n)})`. The classes are the nonempty ones, as in the paper: `{r(ψ)}`, `{p(λ)}` are the values
actually taken. -/
theorem theorem_2_8 :
    ∃ c : ℕ, 0 < c ∧ ∀ {n K : ℕ} (cl : Fin n → Fin K), Function.Surjective cl →
      ∀ rew prob : Fin K → ℝ, (∀ k, 0 ≤ prob k ∧ prob k ≤ 1) →
      let rA : Array ℝ := Array.ofFn rew
      let pA : Array ℝ := Array.ofFn prob
      let sz : Array ℕ := Array.ofFn fun k => (Finset.univ.filter fun i => cl i = k).card
      let tb : Tables := value (dp rA pA sz)
      let r : Fin n → ℝ := fun i => rew (cl i)
      let p : Fin n → ℝ := fun i => prob (cl i)
      let G : Policy n := fun _ A =>
        value (pickClass (basesOf sz) tb.act (Array.ofFn fun i => (cl i).val) (fun _ => true) A)
      cost (dp rA pA sz) ≤ c * (n + 1) ^ (c * K) ∧
      (∀ A : Finset (Fin n), tb.val[value (encode (basesOf sz) (countVec cl A))]! = V r p A) ∧
      IsPolicy G ∧
      ∀ A : Finset (Fin n), (⟨r, p⟩ : Instance n).Rfrom G A = V r p A := by sorry

end ImpatientQPTAS
