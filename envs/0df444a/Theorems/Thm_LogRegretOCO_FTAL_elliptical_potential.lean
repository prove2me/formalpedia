-- Prove2me | Theorems.Thm_LogRegretOCO_FTAL_elliptical_potential
-- name    : LogRegretOCO.FTAL.elliptical_potential
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:40:47.441892+00:00
-- url     : https://prove2.me/theorems/e4604264-075c-4d5b-9de2-cab2196e69ad
-- title:
--   Lemma 11 — the potential bound $\sum_t u_t^\top V_t^{-1} u_t \le n \log(r^2 T/\varepsilon + 1)$
-- statement:
--   Let $u_1, \dots, u_T \in \mathbb{R}^n$ satisfy $\|u_t\| \le r$ for some $r > 0$, let $\varepsilon > 0$, and define
--
--   $$
--   V_t = \sum_{\tau=1}^t u_\tau u_\tau^\top + \varepsilon I_n \qquad (t = 1, \dots, T).
--   $$
--
--   Then
--
--   $$
--   \sum_{t=1}^T u_t^\top V_t^{-1} u_t \le n \log\left(\frac{r^2 T}{\varepsilon} + 1\right).
--   $$
--
--   Each $V_t$ includes the current vector $u_t$. The bound controls the sum of squared lengths of the vectors measured in the metric of the accumulated matrix, and grows only logarithmically in $T$; in the analysis of Follow the Leader it bounds the second term of the regret decomposition (Claim 2 of the paper).
--
--   **Formalization Note** The paper prints $V_t = \sum_{\tau=1}^t u_t u_t^\top + \varepsilon I_n$, a typo for $u_\tau u_\tau^\top$ (its proof uses $V_t - V_{t-1} = u_t u_t^\top$); the Lean uses $u_\tau$. The hypothesis $\varepsilon > 0$, implicit in the paper, is stated (at $\varepsilon = 0$ the matrix can be singular and $r^2T/\varepsilon$ is $0$ in Lean). Vectors are in `EuclideanSpace ℝ (Fin n)` so that $\|\cdot\|$ is the Euclidean norm; matrices act on their coordinate vectors (`WithLp.ofLp`), and $u_\tau u_\tau^\top$ is `Matrix.vecMulVec`.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Mach Learn 69 (2007), p. 190, Lemma 11 (Appendix 2)

import Mathlib

namespace LogRegretOCO.FTAL
theorem elliptical_potential {n : ℕ} (u : ℕ → EuclideanSpace ℝ (Fin n)) (r ε : ℝ) (T : ℕ)
    (hr : 0 < r) (hε : 0 < ε) (hu : ∀ t ∈ Finset.Icc 1 T, ‖u t‖ ≤ r) :
    let V : ℕ → Matrix (Fin n) (Fin n) ℝ := fun t =>
      ∑ τ ∈ Finset.Icc 1 t, Matrix.vecMulVec (WithLp.ofLp (u τ)) (WithLp.ofLp (u τ))
        + ε • (1 : Matrix (Fin n) (Fin n) ℝ)
    ∑ t ∈ Finset.Icc 1 T, dotProduct (WithLp.ofLp (u t)) (Matrix.mulVec (V t)⁻¹ (WithLp.ofLp (u t)))
      ≤ n * Real.log (r ^ 2 * T / ε + 1) := by sorry
end LogRegretOCO.FTAL
