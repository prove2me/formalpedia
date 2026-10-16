-- Prove2me | Theorems.Thm_OAI_PartialPermutation_norm_sum_weighted_sq_le
-- name    : OAI.PartialPermutation.norm_sum_weighted_sq_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:22:51.769524+00:00
-- url     : https://prove2.me/theorems/683f4c90-3e30-43c2-a0a7-c973fe64caf8
-- title:
--   Weighted Cauchy–Schwarz inequality for complex sums with nonnegative weights
-- statement:
--   Let $I$ be a finite index set, let $(p_i)_{i\in I}$ be nonnegative real numbers and let $(c_i)_{i\in I}$ be complex numbers. Then
--   $$
--   \Bigl|\sum_{i\in I}p_i\,c_i\Bigr|^2\le\Bigl(\sum_{i\in I}p_i\Bigr)\Bigl(\sum_{i\in I}p_i\,|c_i|^2\Bigr).
--   $$
--
--   When the weights sum to $1$ this is the convexity bound $|\mathbb{E}\,c|^2\le\mathbb{E}\,|c|^2$ for a weighted average. It is used pointwise to control the squared modulus of a convolution-type sum $\sum_h k(h)f(h^{-1}g)$ with nonnegative $f$ by the total weight and the weighted $\ell^2$ mass of $k$.
--
--   **Formalization Note** The real weights are coerced to complex numbers in the sum on the left, and $|\cdot|$ is the complex modulus.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/CosetCaps.lean#L52-L66

import Mathlib
import Definitions.Def_PartialPermutation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SchurAverage
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ModuleTransport
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Components
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CentralKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CompleteKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RegularRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Plancherel
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TrivialRepresentation

open OAI OAI.PartialPermutation
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical
variable {G : Type*} [Group G] [Fintype G]

theorem OAI.PartialPermutation.norm_sum_weighted_sq_le {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (c : ι → ℂ) :
    ‖∑ i, (p i : ℂ) * c i‖ ^ 2 ≤ (∑ i, p i) * ∑ i, p i * ‖c i‖ ^ 2 := by sorry
