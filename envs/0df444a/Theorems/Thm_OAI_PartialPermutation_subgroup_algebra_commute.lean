-- Prove2me | Theorems.Thm_OAI_PartialPermutation_subgroup_algebra_commute
-- name    : OAI.PartialPermutation.subgroup_algebra_commute
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:33:36.906472+00:00
-- url     : https://prove2.me/theorems/6def77cd-a4e1-4f2f-acb8-add44d824aba
-- title:
--   Group algebras of elementwise commuting subgroups commute inside the group algebra
-- statement:
--   Let $G$ be a group (not necessarily finite) and $\mathbb{C}[G]$ its complex group algebra, whose elements are finitely supported formal sums $\sum_{g\in G}a_g\,g$ with $a_g\in\mathbb{C}$, multiplied bilinearly using the group law on basis elements. For a subgroup $H\le G$, let $\iota_H:\mathbb{C}[H]\to\mathbb{C}[G]$ be the algebra homomorphism induced by the inclusion $H\hookrightarrow G$, so $\iota_H\bigl(\sum_{h\in H}a_h\,h\bigr)=\sum_{h\in H}a_h\,h$.
--
--   Let $H,K\le G$ be subgroups such that $hk=kh$ for all $h\in H$ and $k\in K$. Then for all $a\in\mathbb{C}[H]$ and $b\in\mathbb{C}[K]$,
--
--   $$
--   \iota_H(a)\,\iota_K(b)=\iota_K(b)\,\iota_H(a)\qquad\text{in }\mathbb{C}[G].
--   $$
--
--   Consequently, in every representation of $G$ the operators coming from $\mathbb{C}[H]$ commute with those coming from $\mathbb{C}[K]$. This is used to show that the matrix-algebra models attached to different commuting subgroups act by commuting operators, which bounds the product of their degrees by the dimension of the representation.
--
--   **Formalization Note** $\mathbb{C}[H]$ is `MonoidAlgebra ℂ H` for the subgroup $H$ viewed as a group, and $\iota_H$ is `MonoidAlgebra.mapDomainAlgHom ℂ ℂ H.subtype`. The conclusion is Mathlib's `Commute`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/Restriction.lean#L124-L141

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

open OAI OAI.PartialPermutation
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open scoped MonoidAlgebra BigOperators
variable {G M : Type*} [Group G] [AddCommGroup M] [Module ℂ[G] M]

theorem OAI.PartialPermutation.subgroup_algebra_commute (H K : Subgroup G)
    (h : ∀ g ∈ H, ∀ k ∈ K, Commute g k) (a : ℂ[H]) (b : ℂ[K]) :
    Commute (MonoidAlgebra.mapDomainAlgHom ℂ ℂ H.subtype a)
      (MonoidAlgebra.mapDomainAlgHom ℂ ℂ K.subtype b) := by sorry
