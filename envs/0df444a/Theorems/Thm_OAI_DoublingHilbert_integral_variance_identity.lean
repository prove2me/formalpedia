-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_integral_variance_identity
-- name    : OAI.DoublingHilbert.integral_variance_identity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:37:26.11196+00:00
-- url     : https://prove2.me/theorems/f7f1b3fb-5ca2-42b3-933f-5bdc560159f1
-- title:
--   Mean-square deviation from an arbitrary vector for Hilbert-space-valued random vectors
-- statement:
--   Let $(X,\mu)$ be a probability space and let $H$ be a real Hilbert space with inner product $\langle\cdot,\cdot\rangle$. Let $G:X\to H$ be Bochner integrable with $\|G\|^2$ integrable, and let $m=\int_XG\,d\mu$ be its mean. Then for every vector $a\in H$
--
--   $$
--   \int_X\|G(x)-a\|^2\,d\mu(x)=\int_X\|G(x)\|^2\,d\mu(x)-\|a\|^2-2\,\langle a,\ m-a\rangle .
--   $$
--
--   Equivalently, $\int\|G-a\|^2\,d\mu=\int\|G\|^2\,d\mu-2\langle a,m\rangle+\|a\|^2$; the displayed form isolates the error $m-a$ between the true mean and the reference vector. For $a=m$ it is the variance identity $\int\|G-m\|^2\,d\mu=\int\|G\|^2\,d\mu-\|m\|^2$. Combined with the Cauchy–Schwarz inequality, it shows that a small mean error $\|m-a\|$ and a second moment at most slightly above $\|a\|^2$ force a small mean-square deviation from $a$; this is how averaged derivative bounds are turned into energy bounds in the doubling-subset construction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Extremal.lean#L87-L102

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

theorem OAI.DoublingHilbert.integral_variance_identity {G : X → E} (hG : Integrable G μ)
    (hG2 : Integrable (fun x => ‖G x‖ ^ 2) μ) (a : E) :
    (∫ x, ‖G x - a‖ ^ 2 ∂μ) = (∫ x, ‖G x‖ ^ 2 ∂μ) - ‖a‖ ^ 2 -
      2 * inner ℝ a ((∫ x, G x ∂μ) - a) := by sorry
