-- Prove2me | Theorems.Thm_OmniStores_ReturnRate_proposition_1
-- name    : OmniStores.ReturnRate.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T02:20:16.390313+00:00
-- url     : https://prove2.me/theorems/5396f3a3-026a-47fd-8bce-d4bdf5bfb433
-- title:
--   Proposition 1, p. 12 — higher returns yield fewer stores, broader assortments, and conditionally larger stores
-- statement:
--   Consider two return rates $0<\gamma_1<\gamma_2<1$ under the paper's base-model assumptions, with the retailer strictly preferring stores at both rates. For **any** optimal store counts $n_1,n_2$ and assortments $S_1,S_2$ at the respective rates,
--
--   $$n_2<n_1,\qquad S_1\subseteq S_2,\qquad |S_1|\leq|S_2|.$$
--
--   If $h_r(1-2\gamma_2)>h_o$, then the optimal store size at $\gamma_2$ is at least that at $\gamma_1$. For each $0<\gamma<1$, this condition is equivalent to $\gamma<(h_r-h_o)/(2h_r)$, and it implies $\gamma<1/2$ and $h_o<h_r$.
--
--   This is Proposition 1's comparative-static result for physical-store decisions. It compares actual profit maximizers of (9), including possible ties in product selection.
--
--   **Formalization Note.** “Let $n^*>0$” is read as strict preference for stores, excluding the profit tie at the opening threshold. The store-size condition is evaluated at the larger return rate. “Larger” breadth and store size use weak inequalities, while “fewer” stores is strict. The bounds $0\leq\theta\leq1$ and $k_i\geq0$ make explicit the source's fraction and cost conventions.
-- source:
--   Gao, Agrawal & Cui, “The Effect of Multi-Channel and Omni-Channel Retailing on Physical Stores”, authors' manuscript (PDF of 2020-12-25), p. 12, Proposition 1

import Definitions.Def_OmniStores_ReturnRate_Model

namespace OmniStores.ReturnRate

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Proposition 1, p. 12. Every pair of optimal decisions under strict
preference for stores is compared, including ties in assortment choice. -/
theorem proposition_1 (P : Params ι) (hP : P.Standing) :
    (∀ γ₁ γ₂ : ℝ, γ₁ ∈ Set.Ioo (0 : ℝ) 1 → γ₂ ∈ Set.Ioo (0 : ℝ) 1 → γ₁ < γ₂ →
      PrefersStores P γ₁ → PrefersStores P γ₂ →
      ∀ (n₁ n₂ : ℝ) (S₁ S₂ : Finset ι), IsOptimal P γ₁ n₁ S₁ → IsOptimal P γ₂ n₂ S₂ →
        n₂ < n₁ ∧ S₁ ⊆ S₂ ∧ S₁.card ≤ S₂.card ∧
        (P.ho < P.hr * (1 - 2 * γ₂) → storeSize P γ₁ n₁ S₁ ≤ storeSize P γ₂ n₂ S₂)) ∧
    (∀ γ ∈ Set.Ioo (0 : ℝ) 1,
      (P.ho < P.hr * (1 - 2 * γ) ↔ γ < (P.hr - P.ho) / (2 * P.hr)) ∧
      (P.ho < P.hr * (1 - 2 * γ) → γ < 1 / 2 ∧ P.ho < P.hr)) := by sorry

end OmniStores.ReturnRate
