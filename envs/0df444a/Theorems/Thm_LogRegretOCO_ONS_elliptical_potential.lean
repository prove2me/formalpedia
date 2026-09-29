-- Prove2me | Theorems.Thm_LogRegretOCO_ONS_elliptical_potential
-- name    : LogRegretOCO.ONS.elliptical_potential
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:37:16.269018+00:00
-- url     : https://prove2.me/theorems/c7d1ca71-8d05-4be8-8579-f16d03ba815e
-- title:
--   Lemma 11 — Σₜ uₜᵀVₜ⁻¹uₜ ≤ n log(r²T/ε + 1)
-- statement:
--   Let $u_1,\dots,u_T\in\mathbb R^n$ satisfy $\|u_t\|\le r$ for some $r>0$, let $\varepsilon>0$, and define
--   $$
--   V_t=\sum_{\tau=1}^{t}u_\tau u_\tau^\top+\varepsilon I_n\qquad(t=1,\dots,T).
--   $$
--   Then
--   $$
--   \sum_{t=1}^{T}u_t^\top V_t^{-1}u_t\ \le\ n\log\Big(\frac{r^2T}{\varepsilon}+1\Big).
--   $$
--
--   Applied with $u_t=\nabla_t$, $V_t=A_t$ and $r=G$, this bounds the potential in the regret bound of the Online Newton Step by $n\log(G^2T/\varepsilon+1)$.
--
--   **Formalization Note** The paper prints $V_t=\sum_{\tau=1}^t u_t u_t^\top+\varepsilon I_n$; the summation index is a typo and the statement uses $u_\tau u_\tau^\top$, as the proof does. The hypothesis $\varepsilon>0$ is added: the page leaves it implicit, and without it $V_t$ need not be invertible. Norms are Euclidean and $\log$ is the natural logarithm.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Mach Learn 69 (2007), p. 190, Lemma 11

import Mathlib
import Definitions.Def_LogRegretOCO_ONS_Basic

namespace LogRegretOCO.ONS

/-- Lemma 11 (Hazan–Agarwal–Kale 2007, p. 190). Let `u_1, …, u_T ∈ ℝⁿ` with `‖u_t‖ ≤ r` for some
`r > 0`, let `ε > 0`, and let `V_t = Σ_{τ=1}^t u_τ u_τᵀ + ε Iₙ`. Then
`Σ_{t=1}^T u_tᵀ V_t⁻¹ u_t ≤ n log(r²T/ε + 1)`. -/
theorem elliptical_potential {n : ℕ} (u : ℕ → EuclideanSpace ℝ (Fin n)) (r ε : ℝ)
    (hr : 0 < r) (hε : 0 < ε) (T : ℕ) (hu : ∀ t ∈ Finset.Icc 1 T, ‖u t‖ ≤ r) :
    ∑ t ∈ Finset.Icc 1 T, quadForm (regGram ε u t)⁻¹ (u t) ≤
      n * Real.log (r ^ 2 * T / ε + 1) := by sorry

end LogRegretOCO.ONS
