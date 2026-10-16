-- Prove2me | Theorems.Thm_OAI_PartialPermutation_exists_degree_le_rpow
-- name    : OAI.PartialPermutation.exists_degree_le_rpow
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:36:22.367034+00:00
-- url     : https://prove2.me/theorems/d6017d6d-325a-4ca7-85b1-154d3fcc3b10
-- title:
--   Some factor of a bounded product is at most the $b$-th root of the bound
-- statement:
--   Let $b$ and $D$ be positive integers and let $d_1,\dots,d_b$ be natural numbers. Then
--
--   $$
--   \prod_{i=1}^{b}d_i\le D\quad\Longrightarrow\quad d_i\le D^{1/b}\ \text{ for some } i\in\{1,\dots,b\},
--   $$
--
--   where $D^{1/b}$ is the real $b$-th root of $D$.
--
--   This pigeonhole-type estimate is used when the degrees $d_i$ of pairwise commuting matrix models inside a representation of dimension $D$ have product at most $D$: it singles out a factor whose degree is at most $D^{1/b}$.
--
--   **Formalization Note** The indices run over `Fin b`, the $d_i$ are cast to real numbers, and the root is the real power `(D : ℝ) ^ (1 / (b : ℝ))`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/DegreeEstimates.lean#L18-L36

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
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ConvolutionKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ComponentGeometry
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SmallKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ProjectionCovers
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Restriction
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicMatrices
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicKernels

open OAI OAI.PartialPermutation
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical
attribute [local instance] Classical.propDecidable
open scoped MonoidAlgebra BigOperators
open scoped BigOperators

theorem OAI.PartialPermutation.exists_degree_le_rpow {b D : ℕ} (hb : 0 < b) (hD : 0 < D)
    (d : Fin b → ℕ) (hprod : ∏ i, d i ≤ D) :
    ∃ i, (d i : ℝ) ≤ (D : ℝ) ^ (1 / (b : ℝ)) := by sorry
