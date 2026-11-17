-- Prove2me | Theorems.Thm_OnlineDiscUniv_Supplement_theorem_6_1
-- name    : OnlineDiscUniv.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:29:37.65351+00:00
-- url     : https://prove2.me/theorems/70b6695c-6738-48f6-b541-5a1db0c3be7b
-- title:
--   Theorem 6.1 — independent entries with different laws: $\inf_{\varepsilon}\mathbb E D_{M,N}\to R_\alpha$, the bound (1.1) with $t_4$, the rate of Corollary 1.4, and infeasibility below $R_\alpha$
-- statement:
--   Fix $\alpha>0$ and let $M=M_N$ with $M_N/N\to\alpha$. For each $N$ let the entries $\xi_{N,k,i}$ ($k\le N$, $i\le M_N$) be mutually independent, each with mean zero and variance one; their laws $\nu_{N,k,i}$ may differ. Write $t_\nu(H)=\mathbb E_\nu[|\xi|^4\mathbf 1_{\{|\xi|>H\}}]$ and $R_\alpha=\sqrt\alpha\,V^\infty_{1/\alpha}$.
--
--   1. **Limit.** If the fourth moments are uniformly integrable,
--   $$
--   t_4(H):=\sup_{N,k,i}\mathbb E\big[|\xi_{N,k,i}|^4\mathbf 1_{\{|\xi_{N,k,i}|>H\}}\big]\longrightarrow0\qquad(H\to\infty),\qquad(6.2)
--   $$
--   then $\inf_{\varepsilon\text{ online}}\mathbb E D_{M,N}\to R_\alpha$.
--   2. **Quantitative bound.** For every $\kappa>R_\alpha$, $A>0$ and $K<\infty$ there is a randomized online algorithm, depending only on $(\alpha,\kappa,A,K)$, and constants $C$, $\eta>0$, $N_0$ such that for all $N\ge N_0$, all $M$ with $|M/N-\alpha|<\eta$ and every array of independent entries with laws $\nu_{k,i}$ of mean zero, variance one and $\mathbb E|\xi_{k,i}|^4\le K$,
--   $$
--   \mathbb P(D_{M,N}>\kappa)+\mathbb E(D_{M,N}-\kappa)_+\le C\Big[N^{-A}+\max_{k,i}t_{\nu_{k,i}}(N^{1/3})\Big].
--   $$
--   3. **Rate under higher moments.** For every $q>4$, $K<\infty$ and $\kappa>R_\alpha$ there is one randomized online algorithm and constants $C$, $\eta>0$, $N_0$ such that for all $N\ge N_0$, $|M/N-\alpha|<\eta$ and every such array with $\mathbb E|\xi_{k,i}|^q\le K$,
--   $$
--   \mathbb P(D_{M,N}>\kappa)+\mathbb E(D_{M,N}-\kappa)_+\le C\,N^{-(q-4)/2}.
--   $$
--   4. **Infeasibility below $R_\alpha$.** Under a common fourth-moment bound $\mathbb E|\xi_{N,k,i}|^4\le K$ alone, for every $\kappa<R_\alpha$,
--   $$
--   \sup_{\varepsilon\text{ online}}\mathbb P(D_{M,N}\le\kappa)\longrightarrow0.
--   $$
--
--   This extends Theorem 1.1 and Theorem 1.3 from i.i.d. entries to independent entries whose laws vary, so the Brownian value $R_\alpha$ is universal over heterogeneous inputs as well.
--
--   **Formalization Note** $R_\alpha$ is computed from an arbitrary standard Brownian motion on an arbitrary probability space. Values are in $[0,\infty]$; $\kappa>R_\alpha$ is $R_\alpha<\kappa$ in $[0,\infty]$ and $\kappa<R_\alpha$ is $\kappa<0$ or $\kappa<R_\alpha$ there. The exponent $A$ is named `Aexp`.
--
--   Differences from the source:
--   - generalization: a fixed standard Brownian motion B with its completed natural filtration → every process B with IsBrownianReal B P on every probability space, the values computed on that B; reason: the Brownian control values depend only on the law of B; the source's Brownian motion is one such process
--   - reading: inf / sup over randomized online algorithms (seed space unspecified) → inf / sup over every seed space S : Type with a σ-algebra, every seed probability law and every jointly measurable causal sign map; reason: the paper fixes no seed space; quantifying over all of them is the stronger reading
--   - encoding: ε_k = A_{k,M,N}(U, ξ_1, …, ξ_k) ∈ {−1,+1} → sign maps jointly measurable in (seed, input), constant in columns after k; reason: measurability is implicit in the paper (probabilities and expectations of D_{M,N} must be defined); causality is the online constraint
--   - encoding: entries ξ_{N,k,i} mutually independent, each with mean zero and variance one → laws ν N k i : Measure ℝ, probability measures with x and x² integrable, ∫ x = 0, ∫ x² = 1, input law of the N-th array the product arrayLaw (ν N), seed independent of it; reason: independence across different N plays no role (each statement at size N involves only the N-th array); integrability makes the Bochner integrals the true moments
--   - encoding: M_N/N → α → every integer sequence Mseq with Mseq N / N → α, in (a) and (d); reason: the paper's standing convention of §2.1
--   - reading: "the same construction, depending only on (α, κ, A) and a common fourth-moment bound" (and "one randomized online algorithm" of Corollary 1.4) → a family alg M N with seed unitInterval under Lebesgue measure, chosen with C, η, N₀ before the array; reason: a specific seed space is stronger than an unspecified one; Theorem 1.3's construction is defined for every (M, N)
--   - generalization: (b) under (6.2), (1.1) with t_4(N^{1/3}) = sup over all N, k, i → (b) for every single array whose entry laws lie in MomentClass 4 K, with no (6.2), and with the supremum of t_ν(N^{1/3}) over the entries of the N-th array only; reason: this supremum is at most t_4(N^{1/3}), and the bound at size N concerns only the N-th array, so applying the Lean clause at each N to a sequence satisfying (6.2) and a common fourth-moment bound gives the source's claim
--   - reading: (c) "a common qth-moment bound, q > 4, gives the rate in Corollary 1.4", i.e. O(N^{−(q−4)/2}) along M/N → α → explicit C, η > 0, N₀ with the bound C·N^{−(q−4)/2} for all N ≥ N₀, all |M/N − α| < η and all arrays in MomentClass q K; reason: the rate is obtained by "the previous proof", the uniform argument of Theorem 1.3 / (1.1); the uniform statement implies the along-a-sequence O(·) of (1.2); (6.2) is implied by the common qth-moment bound, so it is not assumed
--   - encoding: κ > R_α, κ < R_α for real κ; A; probabilities, expectations, t_4 → R_α < ofReal κ; κ < 0 ∨ ofReal κ < R_α; the exponent named Aexp; values in ℝ≥0∞, C embedded by ENNReal.ofReal; reason: exactly the order between a real κ and R_α ∈ [0, ∞]; no finiteness of R_α is assumed; same inequalities
-- source:
--   Jo, Lee, Exact Universality of Online Discrepancy, arXiv:2610.00103 (artifact sha256 cb190f127dea2c038b4a22a4787862f82356a983593dfdc3dc3fe3c7c8264ad5), §6.2, Theorem 6.1 and (6.2), p.25 (PDF p.26); (1.1) of Theorem 1.3 and (1.2) of Corollary 1.4, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_OnlineDiscUniv_Ralpha
import Definitions.Def_OnlineDiscUniv_MomentClass
import Definitions.Def_OnlineDiscUniv_OnlineAlg
import Definitions.Def_OnlineDiscUniv_Supplement_optDiscArr

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace OnlineDiscUniv.Supplement

/-- **Theorem 6.1 (independent entries)** (Jo–Lee, *Exact Universality of Online Discrepancy*,
arXiv:2610.00103, artifact sha256 cb190f12…, §6.2, printed p.25, PDF p.26). Let `M_N/N → α`, and
let the entries `ξ_{N,k,i}` be mutually independent, each with mean zero and variance one. Their
distributions may differ. Assume their fourth moments are uniformly integrable:
`t_4(H) := sup_{N,k,i} E[|ξ_{N,k,i}|⁴ 1{|ξ_{N,k,i}| > H}] → 0` as `H → ∞` (6.2). Then the
optimal expected online discrepancy converges to `R_α`. For every `κ > R_α` and `A > 0`, the same
construction, depending only on `(α, κ, A)` and a common fourth-moment bound, satisfies (1.1)
with `t_4` in place of `t_μ`. A common `q`th-moment bound, `q > 4`, gives the rate in
Corollary 1.4. Under a common fourth-moment bound alone, the supremal success probability tends
to zero for every `κ < R_α`.

The four conjuncts are (a) the limit, (b) the quantitative bound (1.1), (c) the rate (1.2) of
Corollary 1.4, (d) the vanishing supremal success probability.

**Formalization Note** The entry laws are `ν N k i` (column `k`, row `i`, both 0-based) and the
input law of the `N`-th array is the product `arrayLaw (ν N)`; the seed is independent of it.
`R_α = √α V^∞_{1/α}` is computed from an arbitrary standard Brownian motion `B` on an arbitrary
probability space (it depends only on the law of `B`); `κ > R_α` is `R_α < ofReal κ` and
`κ < R_α` is `κ < 0 ∨ ofReal κ < R_α`; no finiteness of `R_α` is assumed. "Mean zero, variance
one" is integrability of `x` and `x²` with `∫ x = 0`, `∫ x² = 1`. In (b) and (c) the algorithm is
a family `alg M N` with seed `unitInterval` under Lebesgue measure; it and the constants `C`, `η`,
`N₀` are chosen before the array, and the bound holds for all `N ≥ N₀`, all `M` with
`|M/N − α| < η` and every array whose entry laws lie in the moment class (the uniformity of
(1.1)). In (b) the exponent `A` is `Aexp` and `t_4(N^{1/3})` is replaced by the supremum of
`t_ν(N^{1/3})` over the entries of the `N`-th array, which is at most `t_4(N^{1/3})`; (6.2) is not
assumed in (b), (c), (d). The `O(N^{−(q−4)/2})` of (1.2) is an explicit constant `C`. All
probabilities, expectations and tails are in `ℝ≥0∞`. -/
theorem theorem_6_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (α : ℝ) (hα : 0 < α) :
    (∀ Mseq : ℕ → ℕ, Tendsto (fun N : ℕ => (Mseq N : ℝ) / N) atTop (𝓝 α) →
      ∀ ν : (N : ℕ) → Fin N → Fin (Mseq N) → Measure ℝ,
        (∀ N k i, IsProbabilityMeasure (ν N k i) ∧ Integrable (fun x : ℝ => x) (ν N k i) ∧
          Integrable (fun x : ℝ => x ^ 2) (ν N k i) ∧ ∫ x, x ∂(ν N k i) = 0 ∧
          ∫ x, x ^ 2 ∂(ν N k i) = 1) →
        Tendsto (fun H : ℝ => ⨆ (N : ℕ) (k : Fin N) (i : Fin (Mseq N)), tailMod (ν N k i) H)
          atTop (𝓝 0) →
        Tendsto (fun N : ℕ => optDiscArr (ν N)) atTop (𝓝 (Ralpha P B α))) ∧
    (∀ κ : ℝ, Ralpha P B α < ENNReal.ofReal κ → ∀ Aexp : ℝ, 0 < Aexp → ∀ K : ℝ,
      ∃ alg : (M N : ℕ) → OnlineAlg unitInterval M N, ∃ C η : ℝ, ∃ N₀ : ℕ, 0 < η ∧
        ∀ N M : ℕ, N₀ ≤ N → |(M : ℝ) / N - α| < η →
          ∀ ν : Fin N → Fin M → Measure ℝ, (∀ k i, ν k i ∈ MomentClass 4 K) →
            failProbArr ν (volume : Measure unitInterval) (alg M N) κ +
                expExcessArr ν (volume : Measure unitInterval) (alg M N) κ ≤
              ENNReal.ofReal C * (ENNReal.ofReal ((N : ℝ) ^ (-Aexp)) +
                ⨆ (k : Fin N) (i : Fin M), tailMod (ν k i) ((N : ℝ) ^ ((1 : ℝ) / 3)))) ∧
    (∀ q : ℝ, 4 < q → ∀ K κ : ℝ, Ralpha P B α < ENNReal.ofReal κ →
      ∃ alg : (M N : ℕ) → OnlineAlg unitInterval M N, ∃ C η : ℝ, ∃ N₀ : ℕ, 0 < η ∧
        ∀ N M : ℕ, N₀ ≤ N → |(M : ℝ) / N - α| < η →
          ∀ ν : Fin N → Fin M → Measure ℝ, (∀ k i, ν k i ∈ MomentClass q K) →
            failProbArr ν (volume : Measure unitInterval) (alg M N) κ +
                expExcessArr ν (volume : Measure unitInterval) (alg M N) κ ≤
              ENNReal.ofReal (C * (N : ℝ) ^ (-(q - 4) / 2))) ∧
    (∀ K : ℝ, ∀ Mseq : ℕ → ℕ, Tendsto (fun N : ℕ => (Mseq N : ℝ) / N) atTop (𝓝 α) →
      ∀ ν : (N : ℕ) → Fin N → Fin (Mseq N) → Measure ℝ,
        (∀ N k i, ν N k i ∈ MomentClass 4 K) →
        ∀ κ : ℝ, κ < 0 ∨ ENNReal.ofReal κ < Ralpha P B α →
          Tendsto (fun N : ℕ => optSuccArr (ν N) κ) atTop (𝓝 0)) := by sorry

end OnlineDiscUniv.Supplement
