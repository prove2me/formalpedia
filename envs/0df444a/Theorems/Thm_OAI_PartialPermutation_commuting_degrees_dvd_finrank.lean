-- Prove2me | Theorems.Thm_OAI_PartialPermutation_commuting_degrees_dvd_finrank
-- name    : OAI.PartialPermutation.commuting_degrees_dvd_finrank
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:30:20.899792+00:00
-- url     : https://prove2.me/theorems/206bc290-1ddd-4c71-9d16-a6ae437418e5
-- title:
--   Commuting matrix-algebra actions: the product of the matrix sizes divides the dimension
-- statement:
--   Let $V$ be a finite-dimensional complex vector space and $I$ an index set. For each $i\in I$ let $d_i\ge1$ be an integer and let $A_i\colon M_{d_i}(\mathbb{C})\to\operatorname{End}_{\mathbb C}(V)$ be a homomorphism of unital $\mathbb{C}$-algebras. Assume that the images of different homomorphisms commute: $A_i(X)\,A_j(Y)=A_j(Y)\,A_i(X)$ for all $i\neq j$, $X\in M_{d_i}(\mathbb{C})$ and $Y\in M_{d_j}(\mathbb{C})$. Then for every finite subset $s\subseteq I$,
--   $$
--   \prod_{i\in s}d_i\ \mid\ \dim_{\mathbb C}V .
--   $$
--
--   This is the dimension count behind the classical fact that commuting actions of full matrix algebras split $V$ as a tensor product $\mathbb{C}^{d_{i_1}}\otimes\cdots\otimes\mathbb{C}^{d_{i_k}}\otimes W$. When $V\neq0$ it implies the lower bound $\prod_{i\in s}d_i\le\dim_{\mathbb C}V$ for spaces carrying several commuting matrix-algebra actions.
--
--   **Formalization Note** The maps are Mathlib algebra homomorphisms `Matrix (Fin (d i)) (Fin (d i)) ℂ →ₐ[ℂ] Module.End ℂ V`, so they preserve the identity; positivity of each $d_i$ is the hypothesis `hd`, the index type carries decidable equality, and divisibility is in the natural numbers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/MatrixDegrees.lean#L66-L112

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

open OAI OAI.PartialPermutation
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {ι : Type*} [DecidableEq ι] (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (A : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ →ₐ[ℂ] Module.End ℂ V)
    (hcomm : ∀ i j, i ≠ j → ∀ X Y, Commute (A i X) (A j Y))
include hd A hcomm

theorem OAI.PartialPermutation.commuting_degrees_dvd_finrank (s : Finset ι) :
    (∏ i ∈ s, d i) ∣ Module.finrank ℂ V := by sorry
