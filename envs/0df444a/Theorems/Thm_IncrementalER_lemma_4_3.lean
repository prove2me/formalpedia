-- Prove2me | Theorems.Thm_IncrementalER_lemma_4_3
-- name    : IncrementalER.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:05:04.136398+00:00
-- url     : https://prove2.me/theorems/dcc932f8-20cb-41f2-b9e0-9990c8a0439e
-- title:
--   Lemma 4.3, p.16 — multiplicative weights: $\frac1T\sum_tg_t(v)\le\alpha+\eta\rho^2+\frac{\log n}{\eta T}$
-- statement:
--   Let $V$ be a set of $n\ge1$ coordinates, $T\ge1$, $\rho>0$, $\alpha\in\mathbb R$ and $0<\eta\le1/(2\rho)$. Start from $w_0(v)=1$; in round $t$ let $p_t(v)=w_{t-1}(v)/\sum_uw_{t-1}(u)$, choose a feedback vector $g_t\in\mathbb R^V$ with
--
--   $$|g_t(v)|\le\rho\ \text{for every }v,\qquad\sum_vp_t(v)g_t(v)\le\alpha,$$
--
--   and update $w_t(v)=w_{t-1}(v)\exp(\eta g_t(v))$. Then simultaneously for every $v\in V$,
--
--   $$\frac1T\sum_{t=1}^Tg_t(v)\le\alpha+\eta\rho^2+\frac{\log n}{\eta T}.$$
--
--   The paper uses this bound to compute terminal sets with small average insertion cost (Theorem 4.2).
--
--   Differences from the source:
--   - encoding: feedback vectors chosen in each round → an arbitrary sequence g_1, …, g_T whose constraints are checked against the distributions p_t it generates; reason: this covers feedback chosen adaptively from the past
--   - encoding: 0 < η ≤ 1/(2ρ) → 0 < η and 2ρη ≤ 1; reason: the same condition for ρ > 0
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), Lemma 4.3, p.16

import Mathlib
import Definitions.Def_IncrementalER_mwuWeight

namespace IncrementalER

/-- **Lemma 4.3** (multiplicative weights, [AHK12]).

Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, *Incremental All-Pairs Effective Resistance in
Almost-Linear Time*, STOC 2027 submission (manuscript sha256 a0415fd5…), Lemma 4.3, p.16.

Let `V` be a set of `n ≥ 1` coordinates, `T ≥ 1`, `ρ > 0`, `α ∈ ℝ` and `0 < η ≤ 1/(2ρ)`. Let
`w_0 ≡ 1`, `p_t(v) = w_{t−1}(v)/∑_u w_{t−1}(u)` and `w_t(v) = w_{t−1}(v) exp(η g_t(v))`. If for
every round `t = 1, …, T` the feedback satisfies `|g_t(v)| ≤ ρ` for every `v` and
`∑_v p_t(v) g_t(v) ≤ α`, then for every `v`,
`(1/T) ∑_{t=1}^T g_t(v) ≤ α + ηρ² + log n/(ηT)`.

**Formalization Note.** The feedback is an arbitrary sequence `g : ℕ → V → ℝ`; the constraints are
checked against the distributions `p_t` it generates, so feedback chosen adaptively from the past
is covered. `η ≤ 1/(2ρ)` is written `2ρη ≤ 1`. `log` is the natural logarithm. -/
theorem lemma_4_3 {V : Type*} [Fintype V] [Nonempty V] (T : ℕ) (hT : 1 ≤ T) (ρ α η : ℝ)
    (hρ : 0 < ρ) (hη : 0 < η) (hηρ : 2 * ρ * η ≤ 1) (g : ℕ → V → ℝ)
    (hwidth : ∀ t ∈ Finset.Icc 1 T, ∀ v, |g t v| ≤ ρ)
    (horacle : ∀ t ∈ Finset.Icc 1 T, ∑ v, mwuDist η g t v * g t v ≤ α) (v : V) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, g t v ≤
      α + η * ρ ^ 2 + Real.log (Fintype.card V) / (η * T) := by sorry

end IncrementalER
