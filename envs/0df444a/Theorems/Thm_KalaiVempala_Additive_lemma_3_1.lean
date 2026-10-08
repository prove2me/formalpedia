-- Prove2me | Theorems.Thm_KalaiVempala_Additive_lemma_3_1
-- name    : KalaiVempala.Additive.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:08.234021+00:00
-- url     : https://prove2.me/theorems/eb436c0c-af24-46a3-b234-88d7456180d8
-- title:
--   Lemma 3.1, p. 300 — Σ M(s_{1:t}+p_t)·s_t ≤ M(s_{1:T})·s_{1:T} + D Σ|p_t − p_{t−1}|_∞
-- statement:
--   **Be the perturbed leader.** Let $\mathcal D \subset \mathbb R^n$ be a decision set with $L^1$ diameter at most $D$, that is $|d - d'|_1 = \sum_i |d_i - d'_i| \le D$ for all $d, d' \in \mathcal D$, and let $M$ be an argmin oracle for $\mathcal D$. Let $s_1, s_2, \dots \in \mathbb R^n$ be any state sequence, with $s_{1:t} = s_1 + \dots + s_t$. Then for any $T > 0$ and any vectors $p_0 = 0, p_1, \dots, p_T \in \mathbb R^n$,
--
--   $$\sum_{t=1}^{T} M(s_{1:t} + p_t) \cdot s_t \;\le\; M(s_{1:T}) \cdot s_{1:T} + D \sum_{t=1}^{T} |p_t - p_{t-1}|_\infty .$$
--
--   Perturbing the leader's input by $p_t$ costs at most $D$ times the total movement of the perturbations. With a single perturbation $p_t = p_1$ this bounds the cost of the perturbed "be the leader" algorithm by $\text{min-cost}_T + D|p_1|_\infty$.
--
--   **Formalization Note** $|x|_\infty$ is the Lean norm `‖x‖`, which on `Fin n → ℝ` is the sup norm. "Any state sequence" is taken literally: the states are arbitrary vectors, with no membership in $\mathcal S$. The perturbations form a sequence `p : ℕ → Fin n → ℝ` with `p 0 = 0`; only $p_0, \dots, p_T$ enter the statement.
-- source:
--   Kalai & Vempala, Efficient algorithms for online decision problems, J. Comput. System Sci. 71 (2005), p. 300, Lemma 3.1

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_FPL
import Definitions.Def_KalaiVempala_Additive_Setting

open MeasureTheory OracleRO.ApproxFPL

namespace KalaiVempala.Additive

theorem lemma_3_1 {n : ℕ} (Dset : Set (Fin n → ℝ))
    (M : (Fin n → ℝ) → (Fin n → ℝ)) (hM : IsArgminOracle Dset M)
    (Ddiam : ℝ) (hD : ∀ d ∈ Dset, ∀ d' ∈ Dset, ∑ i, |d i - d' i| ≤ Ddiam)
    (s : ℕ → Fin n → ℝ) (T : ℕ) (hT : 0 < T)
    (p : ℕ → Fin n → ℝ) (hp0 : p 0 = 0) :
    ∑ t ∈ Finset.Icc 1 T, M (prefixSum s t + p t) ⬝ᵥ s t ≤
      M (prefixSum s T) ⬝ᵥ prefixSum s T +
        Ddiam * ∑ t ∈ Finset.Icc 1 T, ‖p t - p (t - 1)‖ := by sorry

end KalaiVempala.Additive
