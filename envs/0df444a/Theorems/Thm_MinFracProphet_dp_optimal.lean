-- Prove2me | Theorems.Thm_MinFracProphet_dp_optimal
-- name    : MinFracProphet.dp_optimal
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:36:21.510311+00:00
-- url     : https://prove2.me/theorems/9497be7a-0b1d-44aa-ab59-2f46c859ab1d
-- title:
--   Appendix B.1: the dynamic program (21)–(22) is optimal among all causal policies
-- statement:
--   Let $n\ge1$, $p>1$ and $0<\ell\le u<\infty$, and let the prices $C_1,\dots,C_n$ be independent, each with a distribution carried by $[\ell,u]$. Let $J_i$ be the cost-to-go functions (21). Then:
--
--   1. $\mathbb E[J_1(0,C_1)]$ is the least expected cost $\mathbb E[\mathrm{ALG}^\pi(C,p)]$ over all causal policies $\pi$, and some policy attains it:
--   $$
--   \mathbb E[J_1(0,C_1)]=\min_\pi\ \mathbb E[\mathrm{ALG}^\pi(C,p)].
--   $$
--   2. A causal policy of the form (22) exists, and every such policy attains the minimum. Form (22) means: at every stage $i<n$ and for all prices in $[\ell,u]^n$, the policy buys an amount
--   $$
--   x_i\in\operatorname*{arg\,min}_{0\le x\le 1-s_i}\ c_ix^p+\mathbb E\bigl[J_{i+1}(s_i+x,C_{i+1})\bigr],
--   $$
--   where $s_i=x_1+\dots+x_{i-1}$ is the amount bought before stage $i$ (and $x_n=1-s_n$).
--
--   The paper takes this from the classical theory of stochastic control (Bertsekas, Prop. 1.3.1). It identifies the optimal adaptive cost, which the lower bound of Theorem 2 evaluates on long-shot instances through Lemma 8.
--
--   **Formalization Note** Stages are 0-based in Lean. Policies are the measurable, non-anticipative maps of the definition module, on all of $\mathbb R^n$. Their expected cost is a lower Lebesgue integral in $[0,\infty]$, and $\mathbb E[J_1(0,C_1)]$ is a Bochner integral embedded by `ENNReal.ofReal`. The last stage needs no condition, because the amounts of every policy sum to $1$.
--
--   Differences from the source:
--   - reading: the optimality of the DP recursion is a classical result (cf. Proposition 1.3.1 of Bertsekas (1995)); the optimal causal policy takes the form (22) → E[J_1(0,C_1)] is the least expected cost over all policies and is attained; a policy satisfying (22) on [ℓ,u]^n exists, and every such policy attains it; reason: the page cites the result without stating it; this is the statement the lower bound uses
--   - reading: D a distribution supported on [ℓ,u] (and the DP of Appendix B.1 for that problem) → independent laws ν_0,…,ν_{n−1}, each a probability measure with ν_i([ℓ,u]ᶜ) = 0, 0 < ℓ ≤ u; reason: “a distribution D” means the tuple D = (D_1,…,D_n) of §1.2; Lemma 8 and the lower bound use the DP only on such instances
--   - reading: (21): J_n(s_n) = c_n(1 − s_n), J_i(s_i) = min c_i(x_i) + E[J_{i+1}(s_i + x_i)] → J_{n−1}(s,c) = c(1−s)^p and J_i(s,c) = inf_{0≤y≤1−s} c y^p + E[J_{i+1}(s+y, C_{i+1})], a function of the state s and the realized price c; reason: c_i(·) is the cost function c_i x^p; the proof’s base case (p.22) reads J_n(s_n) = c_n(1 − s_n)^p
--   - encoding: stages i = 1,…,n → stages i = 0,…,n−1 (Lean stage i is the paper’s stage i+1), law ν ⟨i,_⟩; reason: Lean convention, a shift of the index
--   - encoding: policy π = (π_1,…,π_n), π_i : 𝒞_1 × ⋯ × 𝒞_i → [0,1] with Σ x_i = 1 → measurable maps x i : ℝ^n → [0,1] depending only on c_0,…,c_i, with Σ_i x i c = 1 for every c ∈ ℝ^n; reason: a policy on the supports extends to ℝ^n (clamp the prices into the supports) with the same cost on every instance, so the infimum is unchanged; measurability is the standing convention under which E[ALG^π] is defined
--   - encoding: E[ALG^π] and E[J_1(0,C_1)] → lintegral of ENNReal.ofReal in ℝ≥0∞, and ENNReal.ofReal of a Bochner integral; reason: both are finite here; same values
-- source:
--   Qin, Vardi, Wierman, Minimization Fractional Prophet Inequalities for Sequential Procurement, author manuscript (INFORMS template, sha256 672fa87c…79125d3), Appendix B.1, (21)–(22), p.21, and the optimality paragraph, p.22

import Mathlib
import Definitions.Def_MinFracProphet_Model
import Definitions.Def_MinFracProphet_DynamicProgram

open MeasureTheory

namespace MinFracProphet

/-- **Appendix B.1: optimality of the dynamic programming recursion**, pp.21–22 of J. Qin,
S. Vardi, A. Wierman, *Minimization Fractional Prophet Inequalities for Sequential Procurement*,
author manuscript (sha256 672fa87c…79125d3) (the paper cites Bertsekas, Prop. 1.3.1).

Let `n ≥ 1`, `p > 1`, `0 < ℓ ≤ u`, and let the prices `C_1, …, C_n` be independent with laws
`ν_i` carried by `[ℓ,u]`. Then

1. the expected cost-to-go `E[J_1(0, C_1)]` of the recursion (21) is the least expected cost
   `E[ALG^π(C,p)]` over all causal policies `π`, and some policy attains it;
2. a causal policy following (22) exists: at every stage `i < n` and every price vector in
   `[ℓ,u]^n` it buys an amount `x_i ∈ [0, 1 - s_i]` minimizing `c_i x^p + E[J_{i+1}(s_i + x)]`,
   where `s_i` is the amount bought before stage `i`;
3. every causal policy following (22) attains it.

**Formalization Note** Stages are 0-based (Lean stage `i` is the paper's `i+1`); `costToGo p ν i s c`
is `J_{i+1}(s)` at the realized price `c` of that stage (R9). Policies are the measurable
non-anticipative maps of `IsPolicy` on all of `ℝ^n` (R3), expectations of policies are
lower Lebesgue integrals in `ℝ≥0∞`, the expected cost-to-go is a Bochner integral of a bounded
function. The last stage needs no condition: `x_n = 1 - s_n` holds for every policy because the
amounts sum to `1`. The paper does not prove this statement (R12). -/
theorem dp_optimal (n : ℕ) (hn : 0 < n) (p : ℝ) (hp : 1 < p) (ℓ u : ℝ) (hℓ : 0 < ℓ)
    (hℓu : ℓ ≤ u) (ν : Fin n → Measure ℝ) (hprob : ∀ i, IsProbabilityMeasure (ν i))
    (hsupp : ∀ i, ν i (Set.Icc ℓ u)ᶜ = 0) :
    let followsDP : (Fin n → (Fin n → ℝ) → ℝ) → Prop := fun x =>
      ∀ c : Fin n → ℝ, (∀ j, c j ∈ Set.Icc ℓ u) → ∀ i : Fin n, ∀ h : i.val + 1 < n,
        x i c ∈ Set.Icc 0 (1 - ∑ j ∈ Finset.univ.filter (· < i), x j c) ∧
        ∀ y ∈ Set.Icc 0 (1 - ∑ j ∈ Finset.univ.filter (· < i), x j c),
          c i * x i c ^ p + ∫ c', costToGo p ν (i.val + 1)
              ((∑ j ∈ Finset.univ.filter (· < i), x j c) + x i c) c' ∂(ν ⟨i.val + 1, h⟩) ≤
            c i * y ^ p + ∫ c', costToGo p ν (i.val + 1)
              ((∑ j ∈ Finset.univ.filter (· < i), x j c) + y) c' ∂(ν ⟨i.val + 1, h⟩)
    IsLeast {v | ∃ x, IsPolicy n x ∧ v = EALG p x ν}
        (ENNReal.ofReal (∫ c, costToGo p ν 0 0 c ∂(ν ⟨0, hn⟩))) ∧
      (∃ x, IsPolicy n x ∧ followsDP x) ∧
      ∀ x, IsPolicy n x → followsDP x →
        EALG p x ν = ENNReal.ofReal (∫ c, costToGo p ν 0 0 c ∂(ν ⟨0, hn⟩)) := by sorry

end MinFracProphet
