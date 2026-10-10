-- Prove2me | Theorems.Thm_NAGFlow_PredCorr_corrector_relation
-- name    : NAGFlow.PredCorr.corrector_relation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:30:03.496118+00:00
-- url     : https://prove2.me/theorems/3ecebf62-c0d3-4561-b3c9-53c82789ee03
-- title:
--   §5.2, p. 20 — in the predictor–corrector scheme, x_{k+1} − y_k = (α_k/(1 + α_k))(v_{k+1} − v_k)
-- statement:
--   Let $V$ be a real Hilbert space and let $(x_k,y_k,v_k)$ be a run of the predictor–corrector scheme (83) with step sizes $\alpha_k>0$. Then for every $k$,
--   $$x_{k+1}-y_k=\frac{\alpha_k}{1+\alpha_k}\,(v_{k+1}-v_k).$$
--
--   The identity links the corrector $x_{k+1}$ to the predictor $y_k$ and is what turns the descent inequality for $f$ into (85).
--
--   **Formalization Note.** Only the first and third lines of (83) and $\alpha_k>0$ are used; the run hypothesis carries the whole scheme, as on the page.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, §5.2, display after the bound on ℒ̂_k, p. 20

import Mathlib
import Definitions.Def_NAGFlow_PredCorr_Setting

namespace NAGFlow.PredCorr

/-- The corrector relation of §5.2 (Luo & Chen, arXiv:1909.03145v4, display after the ℒ̂_k bound,
p. 20). For a run `(x, y, v)` of the predictor–corrector scheme (83) with step sizes `α_k > 0`, the
updates for `y_k` and `x_{k+1}` give `x_{k+1} − y_k = (α_k/(1 + α_k))(v_{k+1} − v_k)` for every `k`. -/
theorem corrector_relation {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (gradf : V → V) (μ : ℝ) (α γ : ℕ → ℝ) (hα : ∀ k, 0 < α k)
    (x y v : ℕ → V) (hrun : IsPCRun gradf μ α γ x y v) (k : ℕ) :
    x (k + 1) - y k = (α k / (1 + α k)) • (v (k + 1) - v k) := by sorry

end NAGFlow.PredCorr
