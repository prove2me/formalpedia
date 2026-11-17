-- Prove2me | Theorems.Thm_MultiThinkCoT_Supplement_theorem_8
-- name    : MultiThinkCoT.Supplement.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:59:50.100239+00:00
-- url     : https://prove2.me/theorems/338f0a38-a48c-48ea-8543-8bba5d314159
-- title:
--   Theorem 8 — Algorithm 2 recovers the parity support from $O(k\log(d/\delta)/(1-2\eta)^2)$ adversarially ordered noisy CoTs
-- statement:
--   Fix $d\in\mathbb N$, $k\le d$, and an unknown support $S_\star\subseteq[d]$ with $|S_\star|=k$. The samples $\{(x^{(i)},\tilde z^{(i)})\}_{i=1}^m$ are generated with inputs $x^{(i)}\sim\mathrm{Unif}(\{0,1\}^d)$ i.i.d., orderings $\pi^{(1)},\dots,\pi^{(m)}\in\mathrm{Bij}([k],S_\star)$ chosen by an adversary that sees the whole input sequence $(x^{(1)},\dots,x^{(m)})$, and propagating noise of level $\eta\in[0,1/2)$ during generation. There is a universal constant $C>0$ such that for every $\delta\in(0,1)$, if
--
--   $$
--   m\ \ge\ C\cdot\frac{k}{(1-2\eta)^2}\,\log\frac d\delta,
--   $$
--
--   then the output $\widehat S$ of Algorithm 2 satisfies
--
--   $$
--   \Pr\big[\widehat S=S_\star\big]\ \ge\ 1-\delta .
--   $$
--
--   In fact, with the same probability the scores separate strictly, $\mathrm{score}(j)>\mathrm{score}(j')$ for all $j\in S_\star$ and $j'\notin S_\star$, so the conclusion holds whatever rule breaks ties in the top-$k$ selection. Moreover, at the sample size $m=\lceil C\,k\log(d/\delta)/(1-2\eta)^2\rceil$ the algorithm runs in time $\mathrm{poly}(d,1/(1-2\eta),\log\delta^{-1})$: its cost is at most $C'(d+\lceil1/(1-2\eta)\rceil+\lceil\log(1/\delta)\rceil+2)^e$ for constants $C',e$.
--
--   The theorem shows that the CoT traces make support recovery tractable even when they come from up to $k!$ different generators chosen adversarially per example and without provenance, a regime where learning from the final noisy labels alone is believed to be hard.
--
--   **Formalization Note** Logarithms are natural (another base only changes $C$). The adversary is a deterministic function of the input sequence and does not see the noise. The running time is measured in the unit-cost model of `MultiThinkCoT.Supplement.alg2`.
--
--   Differences from the source:
--   - generalization: $\Pr[\widehat S=S_\star]\ge1-\delta$ for "the $k$ indices with largest score" (tie rule unspecified) → $\Pr[\widehat S=S_\star\text{ and the scores separate strictly}]\ge1-\delta$, with $\widehat S$ computed with a fixed tie-break; reason: strict separation forces $\widehat S=S_\star$ under every tie-breaking rule, so the statement specializes to the source for each reading.
--   - reading: "the algorithm runs in time poly$(d,1/(1-2\eta),\log\delta^{-1})$" → the unit-cost of Algorithm 2 on $m=\lceil Ck\log(d/\delta)/(1-2\eta)^2\rceil$ samples is at most $C'(d+\lceil1/(1-2\eta)\rceil+\lceil\log(1/\delta)\rceil+2)^e$; reason: the running time grows with $m$, so the claim refers to the sample size the theorem asks for.
--   - encoding: orderings "chosen even adversarially based on $(x^{(1)},\dots,x^{(m)})$" → a deterministic map from the input sequence to orderings, universally quantified; reason: a randomized adversary independent of the noise is a mixture of deterministic ones.
-- source:
--   Joshi, Magen, Srebro, Tsilivis, Vardi, Learning to Think from Multiple Thinkers: How Chain-of-Thought Heterogeneity Affects Efficient Learnability, arXiv:2604.24737 (held version, sha256 e663a640…), Appendix G.1, Theorem 8, p.61 (PDF p.61); model pp.59–60

import Mathlib
import Definitions.Def_MultiThinkCoT_Supplement_parityChain
import Definitions.Def_MultiThinkCoT_Supplement_alg2

namespace MultiThinkCoT.Supplement

/-- **Theorem 8 (Guarantee for Algorithm 2)**, Appendix G.1, p.61 (PDF p.61).
N. Joshi, R. Magen, N. Srebro, N. Tsilivis, G. Vardi, *Learning to Think from Multiple Thinkers:
How Chain-of-Thought Heterogeneity Affects Efficient Learnability*, arXiv:2604.24737 (held
version, sha256 e663a640…).

Fix `d ∈ ℕ` and `k ≤ d`, and an unknown `S⋆ ⊆ [d]` with `|S⋆| = k`. The samples
`{(x(i), z̃(i))}_{i=1}^m` are generated under propagating noise with level `η ∈ [0, 1/2)`, and the
generators `(π(1), …, π(m))` may be chosen adversarially based on `(x(1), …, x(m))`. There is a
universal `C > 0` such that for every `δ ∈ (0, 1)`, if `m ≥ C · k/(1 − 2η)² · log(d/δ)`, then the
output `Ŝ` of Algorithm 2 satisfies `Pr[Ŝ = S⋆] ≥ 1 − δ`. The algorithm runs in time
`poly(d, 1/(1 − 2η), log δ⁻¹)`.

**Formalization Note.**
* The data law is `noisySampleLaw d k m S⋆ η adv` (inputs i.i.d. uniform on `{0,1}^d`, orderings
  `adv (x(1..m)) i ∈ Bij([k], S⋆)` for an arbitrary deterministic adversary, noise i.i.d.
  `Bernoulli(η)` independent of the inputs).
* Success event: `Ŝ = S⋆` for Algorithm 2 with its fixed tie-break (`alg2Out`), together with
  strict separation of the scores (`score(j) > score(j')` for all `j ∈ S⋆`, `j' ∉ S⋆`). Strict
  separation makes the top-`k` output equal to `S⋆` under every tie-breaking rule, so the statement
  covers every reading of "the `k` indices with largest score".
* `η ∈ [0, 1/2)` as in the theorem (the closed end `η = 0` included); `k = 0` and `d = 0` allowed.
  `log` is the natural logarithm (another base changes only `C`).
* Runtime: the cost model of `alg2Cost` (unit-cost real arithmetic). The claim is read at the
  sample size the theorem asks for, `m = ⌈C k log(d/δ)/(1 − 2η)²⌉`, with the same `C`: there are
  `C', e` with cost `≤ C' (d + ⌈1/(1 − 2η)⌉ + ⌈log(1/δ)⌉ + 2)^e`.
-/
theorem theorem_8 :
    ∃ C : ℝ, 0 < C ∧
      (∀ d k : ℕ, k ≤ d → ∀ S : Finset (Fin d), S.card = k →
        ∀ η : ℝ, 0 ≤ η → η < 1 / 2 → ∀ δ : ℝ, 0 < δ → δ < 1 →
        ∀ m : ℕ, C * k / (1 - 2 * η) ^ 2 * Real.log (d / δ) ≤ m →
        ∀ adv : (Fin m → Fin d → Bool) → Fin m → (Fin k ≃ S),
          ENNReal.ofReal (1 - δ) ≤ (noisySampleLaw d k m S η adv).toOuterMeasure
            {data | alg2Out data = S ∧
              ∀ j ∈ S, ∀ j' ∉ S, alg2Score data j' < alg2Score data j}) ∧
      (∃ C' e : ℕ, ∀ d k : ℕ, k ≤ d → ∀ η δ : ℝ, 0 ≤ η → η < 1 / 2 → 0 < δ → δ < 1 →
        alg2Cost d k ⌈C * k / (1 - 2 * η) ^ 2 * Real.log (d / δ)⌉₊ ≤
          C' * (d + ⌈1 / (1 - 2 * η)⌉₊ + ⌈Real.log (1 / δ)⌉₊ + 2) ^ e) := by sorry

end MultiThinkCoT.Supplement
