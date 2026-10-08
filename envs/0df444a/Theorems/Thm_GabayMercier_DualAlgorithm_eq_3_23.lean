-- Prove2me | Theorems.Thm_GabayMercier_DualAlgorithm_eq_3_23
-- name    : GabayMercier.DualAlgorithm.eq_3_23
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:13:12.354754+00:00
-- url     : https://prove2.me/theorems/16fb659a-57ef-4828-873f-872927c70470
-- title:
--   (3.23) — uₙ₊₁ = a uₙ + b wₙ with 0 ≤ a < 1, b > 0, Σ wₙ < ∞ gives Σ uₙ < ∞ and uₙ → 0
-- statement:
--   Let $0\le a<1$ and $b>0$, let $(w_n)_{n\ge0}$ be non-negative reals with $\sum_{n=0}^\infty w_n<+\infty$, and let $(u_n)_{n\ge0}$ be real numbers with $u_0\ge0$ and
--   $$u_{n+1}=a\,u_n+b\,w_n\qquad(n\ge0).$$
--   Then $\sum_{n=0}^{\infty}u_n<+\infty$, and consequently $u_n\to0$.
--
--   This elementary lemma is applied with $w_n=|P(y^{n+1}-y^n)|^2$ and $u_0=|P(\lambda^0-\lambda^*)|^2$ to show $P(\lambda^n-\lambda^*)\to0$.
--
--   **Formalization Note.** The paper writes "$w_n>0$" and "positive scalars $u_n$"; we assume $w_n\ge0$ and $u_0\ge0$ (then every $u_n\ge0$), which is more general and is what the application needs, since $w_n=|P(y^{n+1}-y^n)|^2$ may vanish. "For any $N$, $\sum_{n=0}^N u_n<+\infty$" is read as boundedness of the partial sums, i.e. summability of $(u_n)$.
-- source:
--   Gabay & Mercier, IRIA RR-126 (1975), hal-04716124v1, p. 18, (3.23)

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_GabayMercier_DualAlgorithm_Model

open Filter Topology InertialFB.IFB

namespace GabayMercier.DualAlgorithm

/-- (3.23), p. 18: if `uₙ₊₁ = a uₙ + b wₙ` with `0 ≤ a < 1`, `b > 0`, `wₙ ≥ 0` summable and
`u₀ ≥ 0`, then `∑ uₙ < ∞` and `uₙ → 0`. -/
theorem eq_3_23 (a b : ℝ) (u w : ℕ → ℝ) (ha₀ : 0 ≤ a) (ha₁ : a < 1) (hb : 0 < b)
    (hw : ∀ n, 0 ≤ w n) (hws : Summable w) (hu₀ : 0 ≤ u 0)
    (hrec : ∀ n, u (n + 1) = a * u n + b * w n) :
    Summable u ∧ Tendsto u atTop (𝓝 0) := by sorry

end GabayMercier.DualAlgorithm
