-- Prove2me | Theorems.Thm_OAI_PartialPermutation_componentSpace_orthogonal
-- name    : OAI.PartialPermutation.componentSpace_orthogonal
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:24:38.405127+00:00
-- url     : https://prove2.me/theorems/4b6cc9f2-9899-43ca-9c05-296f9cd1885e
-- title:
--   Isotypic components of a unitary representation are mutually orthogonal
-- statement:
--   Let $G$ be a group (not necessarily finite), $V$ a finite-dimensional complex inner product space and $\rho$ a representation of $G$ on $V$ that preserves the inner product: $\langle\rho(g)x,\rho(g)y\rangle=\langle x,y\rangle$ for all $g\in G$ and $x,y\in V$. Regard $V$ as a module over the group algebra $\mathbb{C}[G]$. For a simple submodule $S$, the isotypic component of type $S$ is the sum of all submodules of $V$ isomorphic to $S$; let $\mathcal{C}$ be the set of isotypic components and, for $c\in\mathcal{C}$, let $V_c\subseteq V$ be the underlying complex subspace. Then $(V_c)_{c\in\mathcal C}$ is an orthogonal family of subspaces:
--   $$
--   c\neq c',\quad x\in V_c,\quad y\in V_{c'}\ \Longrightarrow\ \langle x,y\rangle=0 .
--   $$
--
--   For finite $G$ the isotypic components also span $V$, so this yields the orthogonal decomposition $V=\bigoplus_{c}V_c$ of a unitary representation into isotypic components, and in particular $\|v\|^2=\sum_c\|P_cv\|^2$, where $P_c$ is the orthogonal projection onto $V_c$.
--
--   **Formalization Note** The conclusion is Mathlib's `OrthogonalFamily` for the isometric inclusions `(componentSpace ρ c).subtypeₗᵢ`, where `componentSpace ρ c` is the isotypic component `c` (an element of `isotypicComponents ℂ[G] ρ.asModule`) with scalars restricted to the complex numbers. The unitarity hypothesis is written out explicitly rather than as `IsUnitary ρ`, and no finiteness of $G$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/ComponentGeometry.lean#L51-L70

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

open OAI OAI.PartialPermutation
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical
variable {G V : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V)

omit [Fintype G] in
theorem OAI.PartialPermutation.componentSpace_orthogonal
    (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y) :
    OrthogonalFamily ℂ (fun c => componentSpace ρ c) (fun c => (componentSpace ρ c).subtypeₗᵢ) := by sorry
