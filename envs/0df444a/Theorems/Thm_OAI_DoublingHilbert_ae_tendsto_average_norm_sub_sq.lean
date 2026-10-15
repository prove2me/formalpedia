-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_ae_tendsto_average_norm_sub_sq
-- name    : OAI.DoublingHilbert.ae_tendsto_average_norm_sub_sq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:20:50.706274+00:00
-- url     : https://prove2.me/theorems/86f0b94d-3e85-4a99-b145-44f36bcee7de
-- title:
--   Mean-square Lebesgue differentiation for bounded measurable fields on $\mathbb{R}^2$
-- statement:
--   Let $E$ be a normed abelian group (for instance a real normed space), and equip $\mathbb{R}^2$ with Lebesgue measure $\lambda$ and the maximum metric, so that the closed ball of radius $r>0$ about $p$ is the square $\bar B(p,r)=[p_1-r,p_1+r]\times[p_2-r,p_2+r]$.
--
--   **Theorem.** Let $G:\mathbb{R}^2\to E$ be almost everywhere strongly measurable, and suppose there is $M\ge0$ with $\|G(p)\|\le M$ for all $p\in\mathbb{R}^2$. Then for $\lambda$-almost every $p\in\mathbb{R}^2$,
--   $$
--   \lim_{r\to0^+}\ \frac{1}{\lambda(\bar B(p,r))}\int_{\bar B(p,r)}\|G(q)-G(p)\|^2\,dq=0 .
--   $$
--
--   Thus almost every point is a Lebesgue point of $G$ in the mean-square sense. It is applied to the derivative columns of the sheets of a Lipschitz map, which are bounded by the Lipschitz constant; the resulting points are the good points at which derivative data is collected.
--
--   **Formalization Note** The average is Mathlib's set average `⨍ q in Metric.closedBall p r, ‖G q - G p‖ ^ 2`, and the limit is along the right neighbourhood filter `𝓝[>] 0`; the measure on the plane is the product Lebesgue measure `volume`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Derivatives.lean#L28-L62

import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives

open OAI OAI.DoublingHilbert
open MeasureTheory Set Filter
open scoped BigOperators Topology
open MeasureTheory Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E]

theorem OAI.DoublingHilbert.ae_tendsto_average_norm_sub_sq {G : ℝ × ℝ → E}
    (hG : AEStronglyMeasurable G volume) {M : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ p, ‖G p‖ ≤ M) :
    ∀ᵐ p, Tendsto (fun r : ℝ => ⨍ q in Metric.closedBall p r, ‖G q - G p‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by sorry
