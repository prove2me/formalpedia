-- Prove2me | Theorems.Thm_GVRPricing_Structure_intensity_tendsto_lamStar
-- name    : GVRPricing.Structure.intensity_tendsto_lamStar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T12:46:18.381443+00:00
-- url     : https://prove2.me/theorems/88472606-76fc-4eda-af1b-19fc9e3db0ec
-- title:
--   Proof of Theorem 1 — $\lambda^*(n,0^+) = \lambda^*$
-- statement:
--   Let $\lambda(p)$ be a regular demand function with least maximizer $\lambda^*$, let $J$ solve (8), and let $n\ge1$. For each time remaining $t>0$ let $\lambda^*(n,t)$ be an optimal intensity at $(n,t)$. Then
--   $$\lim_{t\to0^+}\lambda^*(n,t) = \lambda^*.$$
--
--   As the deadline approaches, the scarcity value of stock vanishes and the optimal policy approaches the static revenue-maximizing rate; this is the starting point of the inductive step in the paper's proof of Theorem 1.
--
--   **Formalization Note** The paper derives this from $\lim_{t\to0}r'(\lambda^*(n,t))=0$ in (26), which requires differentiability. The limit itself holds under the printed regular-demand assumptions alone, so no further hypothesis is added. The selection $t\mapsto\lambda^*(n,t)$ is arbitrary among optimal intensities.
-- source:
--   Gallego, van Ryzin, Optimal Dynamic Pricing of Inventories with Stochastic Demand over Finite Horizons, Management Science 40(8) (1994), p. 1018 (PDF 20), Appendix, Proof of Theorem 1, inductive step

import Mathlib
import Definitions.Def_GVRPricing_Structure_Model
import Definitions.Def_GVRPricing_Structure_IsHJBSolution

open Filter Topology

namespace GVRPricing.Structure

/-- Proof of Theorem 1 (Gallego–van Ryzin 1994, Appendix, p. 1018): `λ*(n, 0⁺) = λ*`. For a
regular demand function, a solution `J` of (8), a stock `n ≥ 1`, and any choice `ℓ(t)` of an
optimal intensity at `(n, t)` for each `t > 0`, `ℓ(t) → λ*` as the time-to-go `t → 0⁺`. -/
theorem intensity_tendsto_lamStar (M : Model) (J : ℕ → ℝ → ℝ) (hJ : IsHJBSolution M J)
    (n : ℕ) (hn : 1 ≤ n) (ℓ : ℝ → ℝ)
    (hℓ : ∀ t : ℝ, 0 < t → IsOptimalIntensity M J n t (ℓ t)) :
    Tendsto ℓ (𝓝[>] 0) (𝓝 M.lamStar) := by sorry

end GVRPricing.Structure
