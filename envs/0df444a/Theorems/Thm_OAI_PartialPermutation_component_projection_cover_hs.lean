-- Prove2me | Theorems.Thm_OAI_PartialPermutation_component_projection_cover_hs
-- name    : OAI.PartialPermutation.component_projection_cover_hs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:29:32.164598+00:00
-- url     : https://prove2.me/theorems/e3cae2cb-6e2d-48ff-931b-bdcd54df4f8b
-- title:
--   Self-adjoint operators covering all isotypic components dominate the Hilbert–Schmidt norm
-- statement:
--   Let $G$ be a finite group, $V$ a finite-dimensional complex inner product space and $\rho$ a unitary representation of $G$ on $V$, i.e. $\langle\rho(g)x,\rho(g)y\rangle=\langle x,y\rangle$ for all $g,x,y$. Regard $V$ as a $\mathbb{C}[G]$-module and let $\mathcal{C}$ be the set of its isotypic components; for $c\in\mathcal{C}$ let $V_c\subseteq V$ be the underlying subspace. Let $(P_i)_{i\in I}$ be a finite family of self-adjoint operators on $V$ ($P_i^*=P_i$) that covers the isotypic components, in the sense that for every $c\in\mathcal C$ there is an index $i$ with $P_ix=x$ for all $x\in V_c$. Then for every linear operator $A$ on $V$,
--   $$
--   \|A\|_{\mathrm{HS}}^2\le\sum_{i\in I}\|A\,P_i\|_{\mathrm{HS}}^2,
--   $$
--   where $\|X\|_{\mathrm{HS}}^2=\operatorname{Re}\operatorname{tr}(X^*X)$ is the squared Hilbert–Schmidt norm.
--
--   The estimate localizes a Hilbert–Schmidt norm: to bound $\|A\|_{\mathrm{HS}}$ it suffices to bound $A$ composed with each member of a finite family of self-adjoint operators that together act as the identity on every isotypic component. Typical choices of $P_i$ are Fourier transforms of small-type kernels of several subgroups, which are self-adjoint and act as the identity on suitable isotypic components.
--
--   **Formalization Note** The covering hypothesis quantifies over `isotypicComponents ℂ[G] ρ.asModule`, with `componentSpace ρ c` the corresponding subspace; unitarity is `IsUnitary ρ`. The $P_i$ are not required to be projections or to commute with $\rho$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/ProjectionCovers.lean#L101-L118

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
variable {G : Type*} [Group G] [Fintype G]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    {ι : Type*} [Fintype ι] (P : ι → Module.End ℂ V)
    (hP : ∀ i, LinearMap.adjoint (P i) = P i)
    (hcover : ∀ c : isotypicComponents ℂ[G] ρ.asModule,
      ∃ i, ∀ x ∈ componentSpace ρ c, P i x = x)
include ρ hρ hP hcover

theorem OAI.PartialPermutation.component_projection_cover_hs (A : Module.End ℂ V) :
    hsNormSq A ≤ ∑ i, hsNormSq (A * P i) := by sorry
