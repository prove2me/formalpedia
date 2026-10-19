-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_quadratic_form_le_of_multiplicity
-- name    : OAI.MatchingSmoothing.quadratic_form_le_of_multiplicity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:40:49.260603+00:00
-- url     : https://prove2.me/theorems/e3c175a4-21ff-4603-acbe-f0d6150219d0
-- title:
--   Large eigenvalue multiplicities and a small trace of the square bound a symmetric operator from above
-- statement:
--   Let $E$ be a finite-dimensional real inner product space and $B:E\to E$ a self-adjoint linear operator. Let $m,H,a$ be real numbers with $m>0$ and $a\ge0$, and assume:
--
--   1. every nonzero eigenvalue $c$ of $B$ has multiplicity at least $m$, i.e. $\dim\ker(B-c)\ge m$;
--   2. $\operatorname{tr}(B^2)\le H$ and $H\le m\,a^2$.
--
--   Then
--
--   $$
--   \langle x,Bx\rangle\le a\,\|x\|^2\qquad\text{for all }x\in E .
--   $$
--
--   This is a trace method with multiplicities. Without multiplicity information, $\operatorname{tr}(B^2)\le H$ only gives $\lambda_{\max}(B)\le\sqrt H$ (for $H\ge0$). If every nonzero eigenspace has dimension at least $m$, the choice $a=\sqrt{H/m}$ gives $\lambda_{\max}(B)\le\sqrt{H/m}$. For operators on functions of perfect matchings, multiplicity lower bounds come from the dimension of permutation-invariant spaces of high-degree functions, and $\operatorname{tr}(B^2)$ is bounded by a second-moment computation.
--
--   **Formalization Note** The multiplicity hypothesis is required for every real $c\ne0$ with `Module.End.HasEigenvalue B c`, and compares $m$ with `Module.finrank` of `Module.End.eigenspace B c`. The trace is `LinearMap.trace` of `B * B`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/SpectralMultiplicity.lean#L55-L72

import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels

open OAI OAI.MatchingSmoothing
universe u_1
open scoped RealInnerProductSpace
variable {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem OAI.MatchingSmoothing.quadratic_form_le_of_multiplicity (B : Module.End ℝ E) (hB : B.IsSymmetric)
    (m H a : ℝ) (hm : 0 < m) (ha : 0 ≤ a)
    (hdim : ∀ c : ℝ, c ≠ 0 → Module.End.HasEigenvalue B c →
      m ≤ Module.finrank ℝ (Module.End.eigenspace B c))
    (htrace : LinearMap.trace ℝ E (B * B) ≤ H)
    (hHa : H ≤ m * a ^ 2) (x : E) : ⟪x, B x⟫ ≤ a * ‖x‖ ^ 2 := by sorry
