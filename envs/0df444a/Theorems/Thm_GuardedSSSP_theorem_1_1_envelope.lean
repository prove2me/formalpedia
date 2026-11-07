-- Prove2me | Theorems.Thm_GuardedSSSP_theorem_1_1_envelope
-- name    : GuardedSSSP.theorem_1_1_envelope
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:49:24.528554+00:00
-- url     : https://prove2.me/theorems/3aad2e52-7ab5-4ded-928a-3d4c082d88b8
-- title:
--   Proof of Theorem 1.1 — the envelope (19): $g_*(K)\le a_2\Phi(K)\exp(b_2\log^*_2(K+2))$
-- statement:
--   1. $\Phi$ is monotone on $[0,\infty)$.
--   2. For every $c_{\mathrm{core}}\ge1$ there is $C$ with $\big|\log^*_2(c_{\mathrm{core}}(K+1)+2)-\log^*_2(K+2)\big|\le C$ for every natural $K$.
--   3. For every $c_{\mathrm{core}}\ge1$ and $a_1,b_1>0$ there are $a_2,b_2>0$ with the following property. Let $H_*$ be any function on the positive integers obeying (18),
--   $$H_*(z)\le a_1\Phi(z)\exp\big(b_1\log^*_2(z+2)\big)\qquad(z\ge1).$$
--   Then for every natural $K$ the envelope $g_*(K)=1+\max_{1\le z\le\lfloor c_{\mathrm{core}}(K+1)\rfloor}H_*(z)$ of (19) satisfies
--   $$g_*(K)\le a_2\Phi(K)\exp\big(b_2\log^*_2(K+2)\big).$$
--
--   This is the last step of the proof of Theorem 1.1: the per-core cost bound (18) becomes a bound in terms of the benchmark $K$.
--
--   Differences from the source:
--   - reading: H∗(x) := AB^{D∗(x)}f_{D∗(x)}(x), extended by a bounded majorant on small cores, satisfying (18) → every function H : ℕ → ℝ satisfying (18) on z ≥ 1, with a₂, b₂ chosen before H and K; reason: H∗ is defined by the algorithm, which the mission does not formalize; the page's step from (18) to the bound on g∗ uses only (18)
--   - encoding: 1 + max over 1 ≤ z ≤ ⌊c_core(K+1)⌋ of H∗(z) ≤ bound → 1 + H z ≤ bound for every integer z in that range; reason: the range is nonempty since c_core ≥ 1; a bound on the maximum is a bound at every point
--   - encoding: log∗₂(c_core(K + 1) + 2) = log∗₂(K + 2) + O(1) → ∃ C ∀ K, |difference| ≤ C; reason: the meaning of O(1)
-- source:
--   Cai, Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths, STOC 2027 submission (manuscript sha256 bcda0e91…), Proof of Theorem 1.1, display (19) and the bound on g∗, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_GuardedSSSP_LogHierarchy

namespace GuardedSSSP

/-- **Proof of Theorem 1.1**, the envelope (19) and its bound, p.8 (PDF p.9).

Bin Cai, *Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths*, STOC 2027
submission (manuscript sha256 bcda0e91…): "Define the monotone envelope
g∗(K) = 1 + max_{1≤z≤⌊c_core(K+1)⌋} H∗(z). (19) The maximum is over integer scales. … The product Φ is
monotone, and lemma 7.3 gives uniform stability under the fixed multiplier c_core. Also
log∗₂(c_core(K + 1) + 2) = log∗₂(K + 2) + O(1). Thus (18) uniformly over the range in (19) proves
g∗(K) ≤ a₂Φ(K) exp(b₂ log∗₂(K + 2))."

Three clauses:
1. `Φ` is monotone on `[0, ∞)`;
2. for every `c_core ≥ 1` there is `C` with `|log*₂(c_core(K + 1) + 2) − log*₂(K + 2)| ≤ C` for every
   natural `K`;
3. for every `c_core ≥ 1` and `a₁, b₁ > 0` there are `a₂, b₂ > 0` such that for every function `H*` on the
   integer scales obeying (18), `H*(z) ≤ a₁Φ(z)exp(b₁log*₂(z + 2))` for `z ≥ 1`, and every natural `K`,
   `1 + H*(z) ≤ a₂Φ(K)exp(b₂log*₂(K + 2))` for every integer `z` with `1 ≤ z ≤ ⌊c_core(K + 1)⌋`; that is,
   `g*(K) ≤ a₂Φ(K)exp(b₂log*₂(K + 2))`.

**Formalization Note.** `H*` is defined by the algorithm (`A B^{D*(x)} f_{D*(x)}(x)`, extended by a bounded
majorant on small cores), which the mission does not formalize; the statement therefore quantifies over
every `H*` obeying the bound (18), with `a₂, b₂` chosen before `H*` and `K`. A bound on the maximum over a
nonempty finite range is the same as the bound at every point of the range (the range is nonempty because
`c_core ≥ 1`). -/
theorem theorem_1_1_envelope :
    MonotoneOn Phi (Set.Ici 0) ∧
    (∀ c : ℝ, 1 ≤ c → ∃ C : ℝ, ∀ K : ℕ,
      |(logStar (c * ((K : ℝ) + 1) + 2) : ℝ) - (logStar ((K : ℝ) + 2) : ℝ)| ≤ C) ∧
    (∀ c : ℝ, 1 ≤ c → ∀ a₁ b₁ : ℝ, 0 < a₁ → 0 < b₁ → ∃ a₂ b₂ : ℝ, 0 < a₂ ∧ 0 < b₂ ∧
      ∀ H : ℕ → ℝ,
        (∀ z : ℕ, 1 ≤ z → H z ≤ a₁ * Phi z * Real.exp (b₁ * (logStar ((z : ℝ) + 2) : ℝ))) →
        ∀ K : ℕ, ∀ z : ℕ, 1 ≤ z → z ≤ ⌊c * ((K : ℝ) + 1)⌋₊ →
          1 + H z ≤ a₂ * Phi K * Real.exp (b₂ * (logStar ((K : ℝ) + 2) : ℝ))) := by sorry

end GuardedSSSP
