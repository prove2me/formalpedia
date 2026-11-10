-- Prove2me | Theorems.Thm_GoodHypotheses_Proper_lemma_3_6
-- name    : GoodHypotheses.Proper.lemma_3_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:14:15.81069+00:00
-- url     : https://prove2.me/theorems/b8a1ef8e-44af-41aa-ac8a-cca5bd60cdbe
-- title:
--   Lemma 3.6 — Azuma–Hoeffding: Pr[|Σ(X_t − E_t X_t)| ≥ a] ≤ 2exp(−2a²/(B²T))
-- statement:
--   Consider an iterative process producing random variables $X_1,\dots,X_T$ contained in a fixed interval of length $B>0$, and let $E_t$ be the expectation conditioned on the history before step $t$. Then for all $a>0$
--   $$\Pr\Big[\Big|\sum_{t=1}^T(X_t-E_t[X_t])\Big|\ge a\Big]\le2\exp\Big(-\frac{2a^2}{B^2T}\Big).$$
--   It is the concentration tool behind the stochastic MWU bound (Theorem 3.5).
--
--   **Formalization Note.** The process lives on a probability space with a filtration $(\mathcal F_t)_{t\in\mathbb N}$; $X_t$ is $\mathcal F_t$-strongly measurable and $E_t[X_t]=\mathbb E[X_t\mid\mathcal F_{t-1}]$ (Mathlib's `condExp`).
--
--   Differences from the source:
--
--   - reading: an iterative process X_1, …, X_T; E_t = expectation conditioned on the history before step t → a filtration ℱ on a probability space, X_t ℱ_t-strongly measurable for 1 ≤ t ≤ T, E_t[X_t] = P[X_t | ℱ_{t−1}], ℱ_0 arbitrary; reason: the standard meaning of 'history'; the paper does not fix ℱ_0, and the bound holds for every ℱ_0
--   - encoding: contained in a fixed interval of length B → one real c with c ≤ X_t(ω) ≤ c + B for P-almost every ω, for each 1 ≤ t ≤ T; reason: bounded random variables need only satisfy their range bound almost surely; null-set modifications do not affect the probability or conditional expectations
--   - generalization: a finite sequence X_1, …, X_T with the displayed bound defined for T > 0 → T : ℕ, also allowing T = 0; reason: every positive horizon is included; at T = 0 the sum is empty, its tail event is empty for a > 0, and the Lean-total right-hand side is 2
-- source:
--   Aamand, Aliakbarpour, Chen, Silwal, Stevens, Zou, A Good Way to Find Good Hypotheses, STOC 2027 submission (manuscript sha256 a428fbe0…), p. 16, Lemma 3.6

import Mathlib

open MeasureTheory

namespace GoodHypotheses.Proper

/-- Lemma 3.6 (Azuma–Hoeffding, p. 16): random variables `X_1, …, X_T` produced by an iterative
process (adapted to a filtration `ℱ`; `E_t` is the conditional expectation given the history
`ℱ_{t-1}` before step `t`) and almost surely contained in one fixed interval `[c, c + B]` of length `B > 0`
satisfy, for every `a > 0`,
`Pr[|∑_{t=1}^T (X_t − E_t[X_t])| ≥ a] ≤ 2 exp(−2a²/(B²T))`. -/
theorem lemma_3_6 {Ω : Type*} [m₀ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ m₀) (Xs : ℕ → Ω → ℝ) (T : ℕ) (B c a : ℝ) (hB : 0 < B) (ha : 0 < a)
    (hadapt : ∀ t, 1 ≤ t → t ≤ T → StronglyMeasurable[ℱ t] (Xs t))
    (hbound : ∀ t, 1 ≤ t → t ≤ T → ∀ᵐ ω ∂P, c ≤ Xs t ω ∧ Xs t ω ≤ c + B) :
    P {ω | a ≤ |∑ t ∈ Finset.Icc 1 T, (Xs t ω - (P[Xs t | ℱ (t - 1)]) ω)|}
      ≤ ENNReal.ofReal (2 * Real.exp (-2 * a ^ 2 / (B ^ 2 * T))) := by sorry

end GoodHypotheses.Proper
