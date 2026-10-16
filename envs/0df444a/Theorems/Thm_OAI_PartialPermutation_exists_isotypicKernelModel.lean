-- Prove2me | Theorems.Thm_OAI_PartialPermutation_exists_isotypicKernelModel
-- name    : OAI.PartialPermutation.exists_isotypicKernelModel
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:35:00.36954+00:00
-- url     : https://prove2.me/theorems/0e806806-3770-4e00-8593-6cf0e3a2870f
-- title:
--   Isotypic unitary representations admit a matrix model and a normalized character kernel
-- statement:
--   Let $G$ be a finite group and let $M$ be a nonzero finite-dimensional complex inner product space carrying a representation of $G$, given as a module over the group algebra $\mathbb{C}[G]$ that is compatible with complex scalar multiplication. Write $g\cdot x$ for the action of $g\in G$ and $r\cdot x$ for the action of $r\in\mathbb{C}[G]$ on $x\in M$, and let $\mathrm{Mat}_d(\mathbb{C})$ denote the algebra of complex $d\times d$ matrices. Assume:
--
--   1. $M$ is *isotypic* as a $\mathbb{C}[G]$-module: any two simple $\mathbb{C}[G]$-submodules of $M$ are isomorphic;
--   2. the action is *unitary*: $\langle g\cdot x,g\cdot y\rangle=\langle x,y\rangle$ for all $g\in G$ and $x,y\in M$.
--
--   Then $M$ admits an *isotypic kernel model*, that is, there exist
--
--   - a positive integer $d$;
--   - a $\mathbb{C}$-algebra homomorphism $L:\mathrm{Mat}_d(\mathbb{C})\to\mathrm{End}_{\mathbb{C}}(M)$ such that for every matrix $A$ there is $r\in\mathbb{C}[G]$ with $L(A)x=r\cdot x$ for all $x\in M$;
--   - for every $v\in M$, a complex subspace $W\subseteq M$ with $v\in W$, $r\cdot W\subseteq W$ for all $r\in\mathbb{C}[G]$, and $\dim_{\mathbb{C}}W\le d^2$;
--   - a function $k:G\to\mathbb{C}$ satisfying
--
--   $$
--   \sum_{g\in G}|k(g)|^2=\frac{d^2}{|G|},\qquad k(g^{-1})=\overline{k(g)}\ \ (g\in G),\qquad \sum_{g\in G}k(g)\,(g\cdot x)=x\ \ (x\in M).
--   $$
--
--   Such a model packages three facts about an isotypic representation that are needed later: the action of $\mathbb{C}[G]$ contains a unital copy of the $d\times d$ matrix algebra, every vector lies in an invariant subspace of dimension at most $d^2$, and a kernel of $\ell^2$-mass $d^2/|G|$ acts as the identity. It is applied to the restriction of an isotypic component to each of several commuting subgroups, where the matrix copies are compared with the dimension of the component.
--
--   **Formalization Note** The model is the structure `IsotypicKernelModel G M`, which extends `IsotypicMatrixModel ℂ[G] M` (fields `degree`, `degree_pos`, `lift`, `lift_image`, `orbit`) by `kernel`, `kernel_norm`, `kernel_inv`, `kernel_action`; the theorem asserts `Nonempty (IsotypicKernelModel G M)`. The action of $g$ is that of the basis element `MonoidAlgebra.single g 1`, compatibility with scalars is `IsScalarTower ℂ ℂ[G] M`, and isotypy is Mathlib's `IsIsotypic`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/IsotypicKernels.lean#L63-L113

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
open scoped BigOperators
open scoped MonoidAlgebra BigOperators
open scoped MonoidAlgebra BigOperators ComplexConjugate
variable {G M : Type*} [Group G]
    [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    [Module ℂ[G] M] [IsScalarTower ℂ ℂ[G] M]
variable [Fintype G]

theorem OAI.PartialPermutation.exists_isotypicKernelModel [FiniteDimensional ℂ M] [Nontrivial M]
    (h : IsIsotypic ℂ[G] M)
    (hu : ∀ (g : G) (x y : M), inner ℂ ((MonoidAlgebra.single g (1 : ℂ)) • x)
      ((MonoidAlgebra.single g (1 : ℂ)) • y) = inner ℂ x y) :
    Nonempty (IsotypicKernelModel G M) := by sorry
