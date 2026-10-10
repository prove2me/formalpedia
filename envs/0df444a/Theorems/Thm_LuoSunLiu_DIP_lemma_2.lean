-- Prove2me | Theorems.Thm_LuoSunLiu_DIP_lemma_2
-- name    : LuoSunLiu.DIP.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:16:03.272462+00:00
-- url     : https://prove2.me/theorems/f0384bd0-078c-42da-84f2-2fda87afd236
-- title:
--   Lemma 2, p. 17 — M-LinUCB with β_t = β*_t on the pricing PLB is Inner Algorithm B with UCB (2)
-- statement:
--   This statement has two parts.
--
--   1. **LinUCB in closed form.** For $\lambda > 0$, $\beta \ge 0$, any actions $A_s$ and rewards $Z_s$, and any $a \in \mathbb R^d$, the maximum of $\langle\xi, a\rangle$ over the ellipsoid $\{\xi : \|\xi - \hat\xi_{t-1}\|^2_{V_{t-1}(\lambda)} \le \beta\}$ is attained and equals
--   $$\mathrm{LinUCB}_t(a) = \langle\hat\xi_{t-1}, a\rangle + \sqrt\beta\,\|a\|_{V_{t-1}(\lambda)^{-1}} .$$
--   2. **Equivalence of the algorithms.** Let $p_{\max} > 0$, $\lambda > 0$, $d \ge 1$ and an estimate $\hat\theta$ be given. Couple arms, prices and responses with the PLB by $A_t = p_t e_{j_t}$, $\mathcal A_t = \{p\,e_j : j \in \mathcal B_t,\ p = m_j + x_t^\top\hat\theta\}$ and $Z_t = p_t y_t$. Then, on every sample path and for every horizon $T_0$, the actions are a run of M-LinUCB (Algorithm 5) with
--   $$\beta_t = \beta^*_t = p_{\max}^2\Bigl(1 \vee \Bigl(\tfrac{1}{p_{\max}}\sqrt{\lambda d} + \sqrt{2\log(1/\delta) + d\log\tfrac{d\lambda + (t-1)p_{\max}^2}{d\lambda}}\Bigr)^2\Bigr)$$
--   if and only if the arms and prices are a run of Inner Algorithm B (Algorithm 3) with the UCB construction (2) and $\beta_t = \beta^*_t$.
--
--   The equivalence lets the regret analysis of M-LinUCB on a perturbed linear bandit (Lemma 3) be applied to the pricing algorithm.
--
--   **Formalization Note** Part 1 is the step of the proof (pp. 37–38) that identifies $\max_{\xi\in\mathcal C_t}\langle\xi, a\rangle$; it justifies the closed form used in the definition of LinUCB. In part 2, Algorithm 3 is read with forced exploration of unpulled available arms, as the paper's proof of Lemma 2 requires (it sets $0/0 = +\infty$ for unpulled arms, p. 36); with the printed (2) an unpulled arm would get a finite UCB $\sqrt{\beta_t/\lambda}$ and the equivalence would fail. The episode starts at period $1$ ($s_0 = 0$); the responses $y_t$ may be any real numbers.
-- source:
--   Luo, Sun and Liu, arXiv:2109.07340v2, p. 17, Lemma 2 and Algorithm 5; proof pp. 36–38

import Mathlib
import Definitions.Def_SelfNormalizedProcess
import Definitions.Def_LuoSunLiu_DIP_Model
import Definitions.Def_LuoSunLiu_DIP_InnerB
import Definitions.Def_LuoSunLiu_DIP_PLB

open MeasureTheory Matrix

namespace LuoSunLiu.DIP

/-- Lemma 2 (Luo, Sun and Liu, arXiv:2109.07340v2, p. 17; proof pp. 36–38).
(a) For `λ > 0` and `β ≥ 0`, `LinUCB_t(a)` is the maximum of `⟨ξ, a⟩` over the ellipsoid
`𝒞_t(β) = {ξ : ‖ξ - ξ̂_{t-1}‖²_{V_{t-1}(λ)} ≤ β}` (Algorithm 5, line 8).
(b) Under the price-action coupling `A_t = p_t e_{j_t}`, `𝒜_t = {Q_t(p) : p ∈ 𝒮_t}`,
`Z_t = p_t y_t`, M-LinUCB with `β_t = β*_t` runs on the sample path `ω` up to `T₀` exactly when
Inner Algorithm B with the UCB (2) and `β_t = β*_t` does. -/
theorem lemma_2 :
    (∀ {d : ℕ} {Ω : Type*} (lam β : ℝ) (A : ℕ → Ω → Fin d → ℝ) (Z : ℕ → Ω → ℝ)
        (t : ℕ) (ω : Ω) (a : Fin d → ℝ), 0 < lam → 0 ≤ β →
      IsGreatest
        {v : ℝ | ∃ ξ : Fin d → ℝ,
          (ξ - BanditAlgorithm.regularizedLeastSquares d lam A Z (t - 1) ω) ⬝ᵥ
              BanditAlgorithm.regularizedDesignMatrix d lam A (t - 1) ω *ᵥ
                (ξ - BanditAlgorithm.regularizedLeastSquares d lam A Z (t - 1) ω) ≤ β ∧
            v = ξ ⬝ᵥ a}
        (linUCB lam β A Z t ω a)) ∧
    (∀ {d0 d : ℕ} (M : PricingModel d0) (θh : Fin d0 → ℝ) (lam δ : ℝ) {Ω : Type*}
        (x : ℕ → Ω → Fin d0 → ℝ) (j : ℕ → Ω → Fin d) (p y : ℕ → Ω → ℝ) (T0 : ℕ) (ω : Ω),
      0 < M.pmax → 0 < lam → 1 ≤ d →
      (IsMLinUCBRunAt lam (betaStar M.pmax lam d δ)
          (fun t ω => pricingActions M θh d (x t ω))
          (fun t ω => Pi.single (j t ω) (p t ω)) (fun t ω => p t ω * y t ω) T0 ω ↔
        IsInnerBRun M.pmax θh lam (betaStar M.pmax lam d δ) 0 T0
          (fun t => x t ω) (fun t => j t ω) (fun t => p t ω) (fun t => y t ω))) := by sorry

end LuoSunLiu.DIP
