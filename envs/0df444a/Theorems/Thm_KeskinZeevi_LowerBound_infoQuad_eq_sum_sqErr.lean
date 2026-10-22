-- Prove2me | Theorems.Thm_KeskinZeevi_LowerBound_infoQuad_eq_sum_sqErr
-- name    : KeskinZeevi.LowerBound.infoQuad_eq_sum_sqErr
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T02:56:33.448605+00:00
-- url     : https://prove2.me/theorems/77f003dd-6f9a-4dfa-9ab7-c206ae163a05
-- title:
--   C(θ) E[𝒥_t] C(θ)ᵀ equals the cumulative squared pricing error
-- statement:
--   In the single-product linear-demand model with i.i.d. Gaussian demand shocks, fix a policy $\pi$ and a parameter $\theta \in \Theta$. Let $C(\theta) = [-\varphi(\theta)\ \ 1]$. Then for every number of periods $t$,
--   $$C(\theta)\,\mathbb{E}^\pi_\theta[\mathcal{J}_{t}]\,C(\theta)^{\mathsf T} \;=\; \sum_{s=1}^{t}\mathbb{E}^\pi_\theta(p_s-\varphi(\theta))^2 .$$
--   This is the first sentence of the proof of Theorem 1, written with $t$ in place of the paper's $t-1$. It turns inequality (14) of Lemma 1 into inequality (A2).
--
--   **Formalization Note.** The expectation of $\mathcal{J}_t$ is entrywise. The sum runs over Lean periods $0,\dots,t-1$, which are the paper's periods $1,\dots,t$. At $t=0$ both sides are $0$.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, p. 1156, Appendix A.1, proof of Theorem 1, first sentence

import Mathlib
import Definitions.Def_KeskinZeevi_LowerBound_Model
import Definitions.Def_KeskinZeevi_LowerBound_Policy
import Definitions.Def_RobustBooking_Shared_GaussianNoise
import Definitions.Def_KeskinZeevi_LowerBound_Regret
import Definitions.Def_KeskinZeevi_LowerBound_EmpiricalFisher
open RobustBooking.Shared
open MeasureTheory

namespace KeskinZeevi.LowerBound

/-- Keskin and Zeevi 2014, §A.1, proof of Theorem 1, first sentence (p. 1156): since
`C(θ) = [−φ(θ) 1]`, `C(θ) E^π_θ[𝒥_{t−1}] C(θ)ᵀ = Σ_{s=1}^{t−1} E^π_θ(p_s − φ(θ))²`.
Here `t` is the number of periods in `𝒥` (the paper's `t − 1`); the sum runs over Lean periods
`0, …, t − 1`. -/
theorem infoQuad_eq_sum_sqErr (M : Model) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ε : ℕ → Ω → ℝ) (hε : GaussianNoise M.σ P ε)
    (π : Policy M.l M.u) (θ : ℝ × ℝ) (hθ : θ ∈ M.Θ) (t : ℕ) :
    infoQuad P ε π θ t = ∑ s ∈ Finset.range t, sqErr P ε π θ s := by sorry

end KeskinZeevi.LowerBound
