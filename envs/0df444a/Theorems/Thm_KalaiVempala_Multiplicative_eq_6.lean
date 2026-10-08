-- Prove2me | Theorems.Thm_KalaiVempala_Multiplicative_eq_6
-- name    : KalaiVempala.Multiplicative.eq_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:39.441684+00:00
-- url     : https://prove2.me/theorems/dd5652b3-39a4-4555-8ec6-72bfcb513680
-- title:
--   Eq. (6), p. 303 — E[M(s_{1:t−1}+p₁)·s_t] ≤ e^{εA} E[M(s_{1:t}+p₁)·s_t]
-- statement:
--   Let $\mathcal D, \mathcal S \subset \mathbb R^n_+$ be nonnegative decision and state sets, with $|d - d'|_1 \le D$ for $d, d' \in \mathcal D$ and $|s|_1 \le A$ for $s \in \mathcal S$. Let $M$ be a measurable argmin oracle for $\mathcal D$, let $\varepsilon > 0$ and let $\mu_\varepsilon$ be the FPL\* perturbation law. For every state sequence $s_1, s_2, \dots$ and every $t \ge 1$ with $s_t \in \mathcal S$,
--   $$\mathbb E_{p\sim\mu_\varepsilon}\big[M(s_{1:t-1} + p)\cdot s_t\big] \;\le\; e^{\varepsilon A}\; \mathbb E_{p\sim\mu_\varepsilon}\big[M(s_{1:t} + p)\cdot s_t\big].$$
--
--   This is the multiplicative stability step: following the perturbed leader costs at most a factor $e^{\varepsilon A}$ more, period by period, than being the perturbed leader. It is where the nonnegativity restriction of Theorem 1.1(b) enters.
--
--   **Formalization Note** Measurability of $M$ is added because the expectations presuppose it. The diameter bound $D$ is kept so that the integrands are bounded (hence integrable); the bound $R$ of the paper is not used. Only $s_t$ is required to lie in $\mathcal S$; the other states are arbitrary. Expectations are integrals against `laplaceLaw n ε`, the normalised density.
-- source:
--   Kalai & Vempala, Efficient algorithms for online decision problems, J. Comput. System Sci. 71 (2005), p. 303, display (6) and the sentence after (7)

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_FPL
import Definitions.Def_KalaiVempala_Multiplicative_Setting

open MeasureTheory OracleRO.ApproxFPL

namespace KalaiVempala.Multiplicative

theorem eq_6 {n : ℕ} (Dset S : Set (Fin n → ℝ))
    (M : (Fin n → ℝ) → (Fin n → ℝ)) (hM : KalaiVempala.Additive.IsArgminOracle Dset M) (hMmeas : Measurable M)
    (Ddiam : ℝ) (hD : ∀ d ∈ Dset, ∀ d' ∈ Dset, ∑ i, |d i - d' i| ≤ Ddiam)
    (A : ℝ) (hA : ∀ x ∈ S, ∑ i, |x i| ≤ A)
    (hDnn : ∀ d ∈ Dset, ∀ i, 0 ≤ d i) (hSnn : ∀ x ∈ S, ∀ i, 0 ≤ x i)
    (s : ℕ → Fin n → ℝ) (ε : ℝ) (hε : 0 < ε) (t : ℕ) (ht : 1 ≤ t) (hst : s t ∈ S) :
    ∫ p, M (prefixSum s (t - 1) + p) ⬝ᵥ s t ∂(laplaceLaw n ε) ≤
      Real.exp (ε * A) * ∫ p, M (prefixSum s t + p) ⬝ᵥ s t ∂(laplaceLaw n ε) := by sorry

end KalaiVempala.Multiplicative
