-- Prove2me | Theorems.Thm_OmniStores_ReturnRate_decreases_beyond_turning_point
-- name    : OmniStores.ReturnRate.decreases_beyond_turning_point
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T02:20:59.254251+00:00
-- url     : https://prove2.me/theorems/bf816166-11cb-4729-b5a2-a5ded4ec7334
-- title:
--   Proof of Lemma 1, OA p. 1 — profit decreases beyond the first turning point
-- statement:
--   Fix an assortment $S$ and a return rate $0<\gamma<1$. Under the model's standing assumptions, profit strictly decreases as the store count rises above $n^*(\gamma)=t/[2(\gamma h_r+h_o)]$: for $n^*(\gamma)\leq n_1<n_2$,
--
--   $$\pi(\gamma,n_2,S)<\pi(\gamma,n_1,S).$$
--
--   This excludes all larger store counts from a profit maximizer and is the monotonicity claim used in the proof of Lemma 1.
--
--   **Formalization Note.** The result also covers the empty assortment and $h_o=0$; the positive common area $\Omega_0$ makes the decrease strict.
-- source:
--   Gao, Agrawal & Cui, “The Effect of Multi-Channel and Omni-Channel Retailing on Physical Stores”, authors' manuscript (PDF of 2020-12-25), proof of Lemma 1, Online Appendix p. 1 (PDF p. 34)

import Definitions.Def_OmniStores_ReturnRate_ClosedForms

namespace OmniStores.ReturnRate

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Proof of Lemma 1, Online Appendix p. 1: for a fixed assortment, profit
strictly decreases once the store count exceeds the first turning point. -/
theorem decreases_beyond_turning_point (P : Params ι) (hP : P.Standing)
    (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (S : Finset ι) (n₁ n₂ : ℝ)
    (hn₁ : nStar P γ ≤ n₁) (hn : n₁ < n₂) :
    profit P γ n₂ S < profit P γ n₁ S := by sorry

end OmniStores.ReturnRate
