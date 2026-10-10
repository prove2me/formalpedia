-- Prove2me | Theorems.Thm_LuoSunLiu_DIP_lemma_S3
-- name    : LuoSunLiu.DIP.lemma_S3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:15:02.201568+00:00
-- url     : https://prove2.me/theorems/e058699b-7ca9-4e58-ad16-cdd1ed3eced3
-- title:
--   Lemma S3, p. 39 — ‖ξ̇_{t+1} − V_t(λ)⁻¹ Σ_{s≤t} A_s A_sᵀ ξ_s‖_{V_t(λ)} ≤ C₁√(λd)
-- statement:
--   Let $\lambda > 0$ and $C_1 \ge 0$, and let $A_1, \dots, A_t \in \mathbb R^d$ each have exactly one nonzero entry (Condition 3) and $\xi_1, \dots, \xi_t \in \mathbb R^d$ satisfy $\|\xi_s\|_\infty \le C_1$ (Condition 2). Let $V_t(\lambda) = \lambda I + \sum_{s=1}^t A_sA_s^\top$, $V_t = V_t(0)$, and define the shadow parameter $\dot\xi_{t+1} = V_t^+\sum_{s=1}^t A_sA_s^\top\xi_s$ with the Moore–Penrose inverse $V_t^+$. Then
--   $$\Bigl\|\dot\xi_{t+1} - V_t(\lambda)^{-1}\sum_{s=1}^t A_sA_s^\top\xi_s\Bigr\|_{V_t(\lambda)} \le C_1\sqrt{\lambda d},$$
--   where $\|v\|_M = \sqrt{v^\top Mv}$.
--
--   Together with the self-normalized bound (Lemma S4) this gives the confidence ellipsoid of Lemma S5 for the shadow parameter.
--
--   **Formalization Note** Because every $A_s$ has one nonzero entry, $V_t$ is diagonal and $\dot\xi_{t+1}$ is written coordinatewise as $\sum_{s\le t}A_{s,i}^2\xi_{s,i}/\sum_{s\le t}A_{s,i}^2$; Lean's $0/0 = 0$ is the Moore–Penrose value on coordinates never pulled. $\sum_s A_sA_s^\top\xi_s$ is written as $\sum_s\langle A_s, \xi_s\rangle A_s$. The hypothesis $C_1 \ge 0$ is added for the case $t = 0$, where Condition 2 is not invoked; the paper's Condition 2 for all $t$ implies it when $d \ge 1$.
-- source:
--   Luo, Sun and Liu, arXiv:2109.07340v2, p. 39, Lemma S3; proof pp. 39–40

import Mathlib
import Definitions.Def_SelfNormalizedProcess
import Definitions.Def_LuoSunLiu_DIP_PLB

open Matrix

namespace LuoSunLiu.DIP

/-- Lemma S3 (Luo, Sun and Liu, arXiv:2109.07340v2, p. 39; proof pp. 39–40). If the actions
`A_1, …, A_t` each have a single nonzero entry (Condition 3) and `‖ξ_s‖_∞ ≤ C₁` for `s ≤ t`
(Condition 2), then with `V_t(λ) = λI + ∑_{s=1}^t A_s A_sᵀ` and the shadow parameter
`ξ̇_{t+1} = V_t⁺ ∑_{s=1}^t A_s A_sᵀ ξ_s`,
`‖ξ̇_{t+1} - V_t(λ)⁻¹ ∑_{s=1}^t A_s A_sᵀ ξ_s‖_{V_t(λ)} ≤ C₁ √(λd)`. -/
theorem lemma_S3 {d : ℕ} {Ω : Type*} (A ξ : ℕ → Ω → Fin d → ℝ) (C1 lam : ℝ)
    (hC1 : 0 ≤ C1) (hlam : 0 < lam) (t : ℕ) (ω : Ω)
    (hA : ∀ s ∈ Finset.Icc 1 t, IsOneSparse (A s ω))
    (hξ : ∀ s ∈ Finset.Icc 1 t, ∀ i, |ξ s ω i| ≤ C1) :
    mNorm (BanditAlgorithm.regularizedDesignMatrix d lam A t ω)
        (shadowParam A ξ (t + 1) ω -
          (BanditAlgorithm.regularizedDesignMatrix d lam A t ω)⁻¹ *ᵥ
            ∑ s ∈ Finset.Icc 1 t, (A s ω ⬝ᵥ ξ s ω) • A s ω) ≤
      C1 * Real.sqrt (lam * d) := by sorry

end LuoSunLiu.DIP
