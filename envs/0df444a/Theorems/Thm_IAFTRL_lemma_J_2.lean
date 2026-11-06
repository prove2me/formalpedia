-- Prove2me | Theorems.Thm_IAFTRL_lemma_J_2
-- name    : IAFTRL.lemma_J_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:44:56.800486+00:00
-- url     : https://prove2.me/theorems/12d924ce-3861-4bb3-b47c-3cf25704c3f4
-- title:
--   Lemma J.2 — full-history entropy identities for FTRL
-- statement:
--   **Finite part.** Let $\beta_1\le\beta_2\le\cdots$ be positive, let $g_1,g_2,\ldots\in\mathbb R^K$ be arbitrary, $S_0=0$, $S_t=S_{t-1}+g_t$, and let
--   $$
--   q_{t,a}=\frac{e^{-S_{t-1,a}/\beta_t}}{\sum_b e^{-S_{t-1,b}/\beta_t}},\qquad D_t=\langle q_t,g_t\rangle+\beta_t\log\sum_aq_{t,a}e^{-g_{t,a}/\beta_t},\qquad H(q)=-\sum_aq_a\log q_a .
--   $$
--   For every coordinate $u$ and every $T\ge1$,
--   $$
--   \sum_{t\le T}\langle q_t-e_u,g_t\rangle\le\beta_T\log K+\sum_{t\le T}D_t, \tag{J.3}
--   $$
--   $$
--   \sum_{t\le T}\langle q_t-e_u,g_t\rangle\le\beta_1\log K+\sum_{t=2}^T(\beta_t-\beta_{t-1})H(q_t)+\sum_{t\le T}D_t. \tag{J.4}
--   $$
--
--   **Relative part.** Let $\mu$ be a probability measure on a measurable space with measurable singletons, $u$ an atom with $\pi_u=\mu(\{u\})>0$, $h_u=\log(1/\pi_u)$, $g_t$ bounded measurable functions, $S_t=\sum_{s\le t}g_s$, and $q_t$ the Gibbs measure with density $e^{-S_{t-1}/\beta_t}/Z_t$ with respect to $\mu$, $Z_t=\int e^{-S_{t-1}/\beta_t}d\mu$. With $D_t=\int g_t\,dq_t+\beta_t\log\int e^{-g_t/\beta_t}dq_t$ and $D_{\mathrm{KL}}(q_t,\mu)=\int\log\frac{dq_t}{d\mu}\,dq_t$, both
--   $$
--   \sum_{t\le T}\Big(\int g_t\,dq_t-g_t(u)\Big)\le\beta_Th_u+\sum_{t\le T}D_t
--   $$
--   and
--   $$
--   \sum_{t\le T}\Big(\int g_t\,dq_t-g_t(u)\Big)\le\beta_1h_u+\sum_{t=2}^T(\beta_t-\beta_{t-1})\big[h_u-D_{\mathrm{KL}}(q_t,\mu)\big]+\sum_{t\le T}D_t \tag{J.5}
--   $$
--   hold. The coarse bound gives the adversarial regret; the local bound charges only the entropy that remains as the regularization grows.
--
--   **Formalization Note** Rounds are 1-based, as in the paper. Positivity and monotonicity of $\beta$ are required for $t\ge1$.
--
--   Differences from the source:
--   - encoding: nondecreasing $\beta_t$ → $\beta_t>0$ and $\beta_t\le\beta_{t+1}$ for $t\ge1$; reason: the exponential weights $\propto e^{-S/\beta_t}$ are only defined for $\beta_t>0$
--   - encoding: horizon $T$ → $T\ge1$; reason: $\beta_T$ is undefined at $T=0$
--   - reading: $S_t=S_{t-1}+g_t$, $S_0$ not stated → $S_0=0$; reason: the proof uses $F_{\beta_1}(0)=0$, and Algorithm 1 starts from $\hat L_0=0$
--   - reading: (J.5) written as a chain "$\le\ldots\le\ldots$" → two separate bounds on the left-hand side; reason: read as a chain it would assert $\sum_t(\beta_t-\beta_{t-1})D_{\mathrm{KL}}(q_t,\mu)\le0$, false for strictly increasing $\beta$ and $q_t\ne\mu$; the finite analogues (J.3)/(J.4) are separate bounds
--   - encoding: losses $g_t$ in the relative part, unspecified → bounded measurable $g_t$; measurable singletons; reason: makes every integral, $D_t$ and $D_{\mathrm{KL}}$ finite and $\mu(\{u\})$ meaningful; the paper applies it to bounded losses on compact sets
--   - encoding: $D_{\mathrm{KL}}(q_t,\mu)$ → $\int\log(dq_t/d\mu)\,dq_t$ with the explicit Gibbs density; reason: the definition of relative entropy for $q_t\ll\mu$
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Appendix J.1, Lemma J.2, p.205, Eqs. (J.3)–(J.5)

import Mathlib

namespace IAFTRL

open MeasureTheory

/-- **Lemma J.2 (Full-history entropy identities).** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Lemma J.2, p.205: "For
nondecreasing `β_t`, let `q_{t,a} ∝ exp(−S_{t−1,a}/β_t)`, `S_t = S_{t−1} + g_t`, and
`D_t = ⟨q_t, g_t⟩ + β_t log Σ_a q_{t,a} e^{−g_{t,a}/β_t}`. For every fixed coordinate `u`,
`Σ_{t≤T} ⟨q_t − e_u, g_t⟩ ≤ β_T log K + Σ_t D_t`, (J.3)
`Σ_{t≤T} ⟨q_t − e_u, g_t⟩ ≤ β_1 log K + Σ_{t=2}^T (β_t − β_{t−1})H(q_t) + Σ_t D_t`, (J.4)
where `H(q) = −Σ_a q_a log q_a`. For a probability reference `µ`, relative-entropy FTRL
`q_t(da) ∝ e^{−S_{t−1}(a)/β_t}µ(da)`, and an atom `u` of mass `π_u > 0`, the corresponding bounds are
`Σ_t (∫ g_t dq_t − g_t(u)) ≤ β_T log(1/π_u) + Σ_t D_t`,
`≤ β_1h_u + Σ_{t=2}^T (β_t − β_{t−1})[h_u − D_KL(q_t, µ)] + Σ_t D_t`, (J.5)
with `h_u = log(1/π_u)` and the integral definition of `D_t`."

**Finite part.** For positive nondecreasing `β_1 ≤ β_2 ≤ …`, arbitrary losses `g_t ∈ ℝ^K`,
`S_0 = 0`, `S_t = S_{t−1} + g_t`, the exponential weights `q_{t,a} = e^{−S_{t−1,a}/β_t} / Σ_b e^{−S_{t−1,b}/β_t}`
satisfy (J.3) and (J.4) for every coordinate `u` and every horizon `T ≥ 1`.

**Relative part.** For a probability measure `µ` on a measurable space with measurable singletons,
an atom `u` with `π_u = µ({u}) > 0`, bounded measurable losses `g_t`, `S_t = Σ_{s≤t} g_s`, the Gibbs
measures `q_t = (e^{−S_{t−1}/β_t} / Z_t) · µ` with `Z_t = ∫ e^{−S_{t−1}/β_t} dµ`,
`D_t = ∫ g_t dq_t + β_t log ∫ e^{−g_t/β_t} dq_t` and `D_KL(q_t, µ) = ∫ log(dq_t/dµ) dq_t`: both bounds of
(J.5) hold, each bounding the left-hand side `Σ_{t≤T} (∫ g_t dq_t − g_t(u))`.

**Formalization Note.** Rounds are 1-based as in the paper (`β 1 = β_1`, sums over `t ∈ [1, T]`);
`β t > 0` and monotonicity are required for `t ≥ 1` (the exponential weights need `β_t > 0`). In
(J.5) the second "≤" bounds the left side: read as a chain it would assert
`Σ_t (β_t − β_{t−1})D_KL(q_t, µ) ≤ 0`, false whenever `β` increases strictly and some `q_t ≠ µ`.
Boundedness and measurability of `g_t` make every integral, `D_t` and `D_KL` finite. `D_KL` is written
as the explicit integral of the log-density. -/
theorem lemma_J_2 :
    (∀ {K : ℕ} (β : ℕ → ℝ) (g : ℕ → Fin K → ℝ) (u : Fin K) (T : ℕ),
      (∀ t, 1 ≤ t → 0 < β t) → (∀ t, 1 ≤ t → β t ≤ β (t + 1)) → 1 ≤ T →
      let S : ℕ → Fin K → ℝ := fun t a => ∑ s ∈ Finset.Icc 1 t, g s a
      let q : ℕ → Fin K → ℝ := fun t a =>
        Real.exp (-(S (t - 1) a) / β t) / ∑ b, Real.exp (-(S (t - 1) b) / β t)
      let D : ℕ → ℝ := fun t =>
        ∑ a, q t a * g t a + β t * Real.log (∑ a, q t a * Real.exp (-(g t a) / β t))
      let H : (Fin K → ℝ) → ℝ := fun p => -∑ a, p a * Real.log (p a)
      (∑ t ∈ Finset.Icc 1 T, (∑ a, q t a * g t a - g t u) ≤
          β T * Real.log K + ∑ t ∈ Finset.Icc 1 T, D t) ∧
      (∑ t ∈ Finset.Icc 1 T, (∑ a, q t a * g t a - g t u) ≤
          β 1 * Real.log K + ∑ t ∈ Finset.Icc 2 T, (β t - β (t - 1)) * H (q t) +
            ∑ t ∈ Finset.Icc 1 T, D t)) ∧
    (∀ {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] (μ : Measure X)
      [IsProbabilityMeasure μ] (β : ℕ → ℝ) (g : ℕ → X → ℝ) (u : X) (T : ℕ),
      (∀ t, 1 ≤ t → 0 < β t) → (∀ t, 1 ≤ t → β t ≤ β (t + 1)) → 1 ≤ T → 0 < μ {u} →
      (∀ t, Measurable (g t)) → (∀ t, ∃ M : ℝ, ∀ x, |g t x| ≤ M) →
      let S : ℕ → X → ℝ := fun t x => ∑ s ∈ Finset.Icc 1 t, g s x
      let Z : ℕ → ℝ := fun t => ∫ x, Real.exp (-(S (t - 1) x) / β t) ∂μ
      let dens : ℕ → X → ℝ := fun t x => Real.exp (-(S (t - 1) x) / β t) / Z t
      let q : ℕ → Measure X := fun t => μ.withDensity fun x => ENNReal.ofReal (dens t x)
      let D : ℕ → ℝ := fun t =>
        ∫ x, g t x ∂(q t) + β t * Real.log (∫ x, Real.exp (-(g t x) / β t) ∂(q t))
      let KL : ℕ → ℝ := fun t => ∫ x, Real.log (dens t x) ∂(q t)
      let h : ℝ := Real.log (1 / (μ {u}).toReal)
      (∑ t ∈ Finset.Icc 1 T, (∫ x, g t x ∂(q t) - g t u) ≤
          β T * h + ∑ t ∈ Finset.Icc 1 T, D t) ∧
      (∑ t ∈ Finset.Icc 1 T, (∫ x, g t x ∂(q t) - g t u) ≤
          β 1 * h + ∑ t ∈ Finset.Icc 2 T, (β t - β (t - 1)) * (h - KL t) +
            ∑ t ∈ Finset.Icc 1 T, D t)) := by sorry

end IAFTRL
