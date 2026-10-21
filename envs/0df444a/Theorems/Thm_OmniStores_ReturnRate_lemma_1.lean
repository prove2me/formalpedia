-- Prove2me | Theorems.Thm_OmniStores_ReturnRate_lemma_1
-- name    : OmniStores.ReturnRate.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T02:21:20.977853+00:00
-- url     : https://prove2.me/theorems/c41dbcbd-5463-4a77-b964-cf790d2b6a2c
-- title:
--   Lemma 1, p. 11 — the threshold for opening stores and optimal positive-store decisions
-- statement:
--   Under the standing assumptions, there is a threshold $G$, depending only on the model parameters, such that the retailer strictly prefers physical stores exactly when $\gamma>G$ for $0<\gamma<1$. Above the threshold the optimal positive-store count is
--
--   $$n^*=\frac{t}{2(\gamma h_r+h_o)},$$
--
--   and the strict-criterion assortment is $I_s^*=\{i\in I:k_i\gamma[2(\gamma h_r+h_o)/t]\theta D_i>\xi[\alpha_i+\beta_i((2h_o/t)(1-\theta)D_i+(1-\gamma)[2(\gamma h_r+h_o)/t]\theta D_i)]\}$. It is nonempty and optimal at $n^*$. Every optimal decision above the threshold uses this store count and includes $I_s^*$. At or below the threshold, online-only operation is optimal.
--
--   This threshold and decision characterization supplies the positive-store regime for Proposition 1.
--
--   **Formalization Note.** “Prefers” means strict profit superiority over online-only operation. An item with zero incremental profit may also be carried by an optimal assortment, so inclusion of $I_s^*$ is asserted rather than unique equality.
-- source:
--   Gao, Agrawal & Cui, “The Effect of Multi-Channel and Omni-Channel Retailing on Physical Stores”, authors' manuscript (PDF of 2020-12-25), p. 11, Lemma 1; proof, Online Appendix p. 1 (PDF p. 34)

import Definitions.Def_OmniStores_ReturnRate_ClosedForms

namespace OmniStores.ReturnRate

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Lemma 1, p. 11, together with its online-only case from the proof on
Online Appendix p. 1. The threshold is uniform in the return rate. Products
with zero incremental profit may be carried by another optimal assortment. -/
theorem lemma_1 (P : Params ι) (hP : P.Standing) :
    ∃ G : ℝ, ∀ γ ∈ Set.Ioo (0 : ℝ) 1,
      (PrefersStores P γ ↔ G < γ) ∧
      (G < γ →
        IsOptimal P γ (P.t / (2 * (γ * P.hr + P.ho))) (IStarPrinted P γ) ∧
        (IStarPrinted P γ).Nonempty ∧
        ∀ n S, IsOptimal P γ n S →
          n = P.t / (2 * (γ * P.hr + P.ho)) ∧ IStarPrinted P γ ⊆ S) ∧
      (γ ≤ G → IsOptimal P γ 0 ∅) := by sorry

end OmniStores.ReturnRate
