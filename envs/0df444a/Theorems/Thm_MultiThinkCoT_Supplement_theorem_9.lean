-- Prove2me | Theorems.Thm_MultiThinkCoT_Supplement_theorem_9
-- name    : MultiThinkCoT.Supplement.theorem_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:00:20.860647+00:00
-- url     : https://prove2.me/theorems/b852acdc-12e8-46a3-979a-89861efea954
-- title:
--   Theorem 9 — Fano lower bound $m\ge((1-\delta)\log\binom dk-1)/\log(k+1)$ for recovering the support from uniformly random CoT generators
-- statement:
--   Fix $d\in\mathbb N$ and $1\le k\le d-1$. Let $S_\star$ be drawn uniformly from $\binom{[d]}{k}$ and, given $S_\star$, draw $m$ i.i.d. samples $(x^{(i)},z^{(i)})$, where $x^{(i)}\sim\mathrm{Unif}(\{0,1\}^d)$ and $z^{(i)}$ is the noiseless CoT of a random generator $\pi^{(i)}\sim\mathrm{Unif}(\mathrm{Bij}([k],S_\star))$, i.i.d. Then any (possibly randomized) estimator $\widehat S=\widehat S\big((x^{(i)},z^{(i)})_{i=1}^m\big)$ achieving $\Pr[\widehat S=S_\star]\ge1-\delta$, the probability being over $S_\star$, the samples and the estimator's randomness, requires
--
--   $$
--   m\ \ge\ \frac{(1-\delta)\log_2\binom dk-1}{\log_2(k+1)} ,
--   $$
--
--   and, for $k\le d/2$,
--
--   $$
--   m\ \ge\ \frac{(1-\delta)\,k\log_2(d/k)-1}{\log_2(k+1)} .
--   $$
--
--   Together with Theorem 8, this shows that $\Omega(k\log d)$ samples are nearly necessary even when each generator is chosen uniformly at random and the CoT is noiseless, whereas a single fixed generator needs only $O(\log(d/\delta))$ samples.
--
--   **Formalization Note** $\delta$ is an arbitrary real number, as in the paper. The estimator is any map from datasets to probability distributions over subsets of $[d]$ and may depend on $d,k,m$.
--
--   Differences from the source:
--   - reading: $\log$ (base not stated) → $\log_2$ throughout; reason: the $-1$ is the one bit of Fano's inequality in its standard form (35), and the base-2 reading is the stronger one (it implies the natural-log reading because $\ln2<1$).
--   - encoding: a possibly randomized estimator → a map from datasets to `PMF (Finset (Fin d))`; reason: an estimator with internal randomness is exactly a data-dependent distribution over outputs.
-- source:
--   Joshi, Magen, Srebro, Tsilivis, Vardi, Learning to Think from Multiple Thinkers: How Chain-of-Thought Heterogeneity Affects Efficient Learnability, arXiv:2604.24737 (held version, sha256 e663a640…), Appendix G.2, Theorem 9, p.63 (PDF p.63)

import Mathlib
import Definitions.Def_MultiThinkCoT_Supplement_recoveryProb

namespace MultiThinkCoT.Supplement

/-- **Theorem 9 (Information-theoretic limit from a random CoT generator)**, Appendix G.2, p.63
(PDF p.63).
N. Joshi, R. Magen, N. Srebro, N. Tsilivis, G. Vardi, *Learning to Think from Multiple Thinkers:
How Chain-of-Thought Heterogeneity Affects Efficient Learnability*, arXiv:2604.24737 (held
version, sha256 e663a640…).

Fix `d ∈ ℕ` and `1 ≤ k ≤ d − 1`. Let `S⋆` be uniform on `([d] choose k)`; given `S⋆`, draw `m`
i.i.d. samples `(x(i), z(i))`, where `z(i)` is the CoT of a random generator
`π(i) ∼iid Bij([k], S⋆)`. Then any (possibly randomized) estimator `Ŝ` with
`Pr[Ŝ = S⋆] ≥ 1 − δ` requires `m ≥ ((1 − δ) log C(d, k) − 1)/log(k + 1)`, and for `k ≤ d/2`,
`m ≥ ((1 − δ) k log(d/k) − 1)/log(k + 1)`.

**Formalization Note.**
* The model is noiseless (`η = 0`): `recoveryProb d k m E` is `Pr[Ŝ = S⋆]` over `S⋆`, the samples
  (`x(i) ∼ Unif({0,1}^d)`, `π(i) ∼ Unif(Bij([k], S⋆))` independent, `z(i)` the exact partial
  parities `z_1, …, z_k`) and the estimator's randomness; the estimator is any map from datasets to
  `PMF (Finset (Fin d))` and may depend on `d, k, m`.
* Logarithms are base 2 (`Real.logb 2`): the `−1` is Fano's `+1` bit (the binary entropy is at
  most one bit in the standard form (35)). The natural-log reading `(1 − δ) ln C(d,k) − 1` is the
  weaker statement, since `ln 2 < 1`.
* `δ : ℝ` is unrestricted, as in the paper (for `δ ≥ 1` the bound is trivial, for `δ < 0` the
  hypothesis cannot hold). `k ≤ d − 1` is `k + 1 ≤ d`, `k ≤ d/2` is `2k ≤ d`.
-/
theorem theorem_9 :
    ∀ d k : ℕ, 1 ≤ k → k + 1 ≤ d → ∀ m : ℕ,
      ∀ E : (Fin m → (Fin d → Bool) × (Fin k → Bool)) → PMF (Finset (Fin d)), ∀ δ : ℝ,
      1 - δ ≤ recoveryProb d k m E →
        ((1 - δ) * Real.logb 2 (d.choose k) - 1) / Real.logb 2 (k + 1) ≤ m ∧
        (2 * k ≤ d →
          ((1 - δ) * k * Real.logb 2 ((d : ℝ) / k) - 1) / Real.logb 2 (k + 1) ≤ m) := by sorry

end MultiThinkCoT.Supplement
