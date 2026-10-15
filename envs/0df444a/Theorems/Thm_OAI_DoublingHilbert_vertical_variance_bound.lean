-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_vertical_variance_bound
-- name    : OAI.DoublingHilbert.vertical_variance_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:38:06.646149+00:00
-- url     : https://prove2.me/theorems/4119f40e-3e71-4548-90bb-3dcd0e7fcc45
-- title:
--   Mean-square deviation bound from an affine barrier between two squared norms
-- statement:
--   Let $(X,\mu)$ be a probability space and $E$ a real Hilbert space (a complete real inner product space). Let $G,H:X\to E$ be Bochner integrable maps such that $\|G\|^2$ and $\|H\|^2$ are integrable, and write $\bar G=\int_X G\,d\mu$ and $\bar H=\int_X H\,d\mu$ for their means. Let $K\subseteq\mathbb{R}^2$ be a set with $(\|G(x)\|^2,\|H(x)\|^2)\in K$ for $\mu$-almost every $x$, and let $A,B,\varepsilon,C,D\in\mathbb{R}$ with $C\ge0$ be such that every point $(s,s')\in K$ satisfies the affine barrier $s'\le B+\varepsilon+C(A-s)$. Then for all $u,v\in E$ with $\|u\|\le D$ and $\|v\|\le D$,
--
--   $$
--   \int_X\|H-v\|^2\,d\mu\;\le\;B-\|v\|^2+\varepsilon+C\Big(A-\|u\|^2+2D\,\|\bar G-u\|\Big)+2D\,\|\bar H-v\|.
--   $$
--
--   The barrier says that the second squared norm can exceed $B+\varepsilon$ only in proportion to the amount by which the first squared norm falls below $A$. The theorem turns this pointwise constraint into a quantitative $L^2$ estimate: if the means $\bar G,\bar H$ are close to $u,v$ and $\|u\|^2,\|v\|^2$ are close to $A,B$, then $\int_X\|H-v\|^2\,d\mu$ is at most $\varepsilon$ plus small error terms. In the construction of a doubling subset of $\ell^2$ with no bi-Lipschitz embedding into Euclidean space, $G$ and $H$ are the two partial derivatives of a strip-selected sheet, $K$ is the compact set of squared derivative norms and $(A,B)$ is its lexicographic maximum; the estimate controls the vertical energy.
--
--   **Formalization Note** All integrals are Bochner integrals with respect to the probability measure `μ`, and the membership in $K$ is only required almost everywhere. No sign conditions are imposed on $A$, $B$, $\varepsilon$ or $D$ (the hypotheses $\|u\|,\|v\|\le D$ force $D\ge0$).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Extremal.lean#L147-L170

import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets

open OAI OAI.DoublingHilbert
open MeasureTheory Set Filter
open scoped BigOperators Topology
open MeasureTheory
open scoped BigOperators
variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [IsProbabilityMeasure μ] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

theorem OAI.DoublingHilbert.vertical_variance_bound
    {G H : X → E} (hG : Integrable G μ) (hG2 : Integrable (fun x => ‖G x‖ ^ 2) μ)
    (hH : Integrable H μ) (hH2 : Integrable (fun x => ‖H x‖ ^ 2) μ)
    {K : Set (ℝ × ℝ)} (hvalues : ∀ᵐ x ∂μ, (‖G x‖ ^ 2, ‖H x‖ ^ 2) ∈ K)
    {A B ε C D : ℝ} (hC : 0 ≤ C)
    (hbarrier : ∀ p ∈ K, p.2 ≤ B + ε + C * (A - p.1))
    (u v : E) (hu : ‖u‖ ≤ D) (hv : ‖v‖ ≤ D) :
    (∫ x, ‖H x - v‖ ^ 2 ∂μ) ≤ B - ‖v‖ ^ 2 + ε +
      C * (A - ‖u‖ ^ 2 + 2 * D * ‖(∫ x, G x ∂μ) - u‖) +
      2 * D * ‖(∫ x, H x ∂μ) - v‖ := by sorry
