-- Prove2me | Theorems.Thm_KalaiVempala_Additive_eq_5
-- name    : KalaiVempala.Additive.eq_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:11.079232+00:00
-- url     : https://prove2.me/theorems/88719cdd-fc76-4a90-a6a3-3770aab995a8
-- title:
--   (5), p. 300 — Σ M(s_{1:t}+p₁)·s_t ≤ M(s_{1:T})·s_{1:T} + D|p₁|_∞ ≤ M(s_{1:T})·s_{1:T} + D/ε
-- statement:
--   **A single perturbation from the cube.** Let $\mathcal D \subset \mathbb R^n$ have $L^1$ diameter at most $D$ and let $M$ be an argmin oracle for $\mathcal D$. Let $s_1, s_2, \dots \in \mathbb R^n$ be any state sequence with $s_{1:t} = s_1 + \dots + s_t$, let $\varepsilon > 0$, and let $p_1$ be a point of the cube $[0, 1/\varepsilon]^n$. Then for every $T$,
--
--   $$\sum_{t=1}^{T} M(s_{1:t} + p_1) \cdot s_t \;\le\; M(s_{1:T}) \cdot s_{1:T} + D\,|p_1|_\infty \;\le\; M(s_{1:T}) \cdot s_{1:T} + \frac{D}{\varepsilon}.$$
--
--   This is the first half of the proof of Theorem 1.1(a): when FPL($\varepsilon$) uses the same perturbation $p_1$ in every period, being the perturbed leader costs at most $D/\varepsilon$ more than the best decision in hindsight. Both inequalities of the chain are asserted.
--
--   **Formalization Note** The page prints $M(s_t + p_1)$ in the sum; it is obtained from Lemma 3.1 with $p_t = p_1$, which gives $M(s_{1:t} + p_1)$, and the text says it applies Lemma 3.1, so the statement uses $s_{1:t}$. The hypothesis $\varepsilon > 0$ is added because the page divides by $\varepsilon$. $|p_1|_\infty$ is the Lean sup norm `‖p₁‖`, and the cube is `Set.Icc 0 (fun _ => ε⁻¹)`. $T$ is unrestricted (at $T = 0$ the chain reads $0 \le D|p_1|_\infty \le D/\varepsilon$).
-- source:
--   Kalai & Vempala, Efficient algorithms for online decision problems, J. Comput. System Sci. 71 (2005), p. 300, proof of Theorem 1.1(a), display (5)

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_FPL
import Definitions.Def_KalaiVempala_Additive_Setting

open MeasureTheory OracleRO.ApproxFPL

namespace KalaiVempala.Additive

theorem eq_5 {n : ℕ} (Dset : Set (Fin n → ℝ))
    (M : (Fin n → ℝ) → (Fin n → ℝ)) (hM : IsArgminOracle Dset M)
    (Ddiam : ℝ) (hD : ∀ d ∈ Dset, ∀ d' ∈ Dset, ∑ i, |d i - d' i| ≤ Ddiam)
    (s : ℕ → Fin n → ℝ) (T : ℕ) (ε : ℝ) (hε : 0 < ε)
    (p₁ : Fin n → ℝ) (hp₁ : p₁ ∈ Set.Icc (0 : Fin n → ℝ) (fun _ => ε⁻¹)) :
    ∑ t ∈ Finset.Icc 1 T, M (prefixSum s t + p₁) ⬝ᵥ s t ≤
        M (prefixSum s T) ⬝ᵥ prefixSum s T + Ddiam * ‖p₁‖ ∧
      M (prefixSum s T) ⬝ᵥ prefixSum s T + Ddiam * ‖p₁‖ ≤
        M (prefixSum s T) ⬝ᵥ prefixSum s T + Ddiam / ε := by sorry

end KalaiVempala.Additive
