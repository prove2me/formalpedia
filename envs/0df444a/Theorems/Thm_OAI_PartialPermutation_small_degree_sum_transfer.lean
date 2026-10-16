-- Prove2me | Theorems.Thm_OAI_PartialPermutation_small_degree_sum_transfer
-- name    : OAI.PartialPermutation.small_degree_sum_transfer
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:37:24.759433+00:00
-- url     : https://prove2.me/theorems/cfb95bc1-d1a6-4294-805c-b51ecda54e43
-- title:
--   Coset caps on commuting subgroups bound the Hilbert–Schmidt norm by small-degree sums
-- statement:
--   Let $G$ be a finite group and $\rho$ an irreducible representation of $G$ on a finite-dimensional complex inner product space $V$ that is unitary: $\langle\rho(g)x,\rho(g)y\rangle=\langle x,y\rangle$ for all $g\in G$ and $x,y\in V$. Let $b\ge1$ and let $H_1,\dots,H_b$ be subgroups of $G$ whose elements commute across different indices: $gk=kg$ whenever $i\neq j$, $g\in H_i$ and $k\in H_j$. Let $f:G\to\mathbb{R}$ be nonnegative and $B\in\mathbb{R}$, and assume that every $H_i$ satisfies the *left-coset cap*
--
--   $$
--   \sum_{h\in H_i}f(gh)\le\frac{B}{[G:H_i]}\qquad\text{for all }g\in G .
--   $$
--
--   We use the following notation.
--   - $\hat f(\rho)=\sum_{g\in G}f(g)\,\rho(g)$ is the Fourier transform of $f$ at $\rho$.
--   - $\|A\|_{\mathrm{HS}}^2=\operatorname{Re}\operatorname{tr}(A^*A)$ is the squared Hilbert–Schmidt norm of an operator $A$ on $V$.
--   - $\operatorname{mass}(f)=\sum_{g\in G}f(g)$.
--   - For a finite group $H$ and $R\in\mathbb{R}$, $\Sigma_H(R)=\sum_{\pi}d_\pi^2$, the sum over the irreducible representations $\pi$ of $H$, up to isomorphism, whose degree $d_\pi$ satisfies $d_\pi\le R$.
--
--   Then
--
--   $$
--   \dim V\cdot\|\hat f(\rho)\|_{\mathrm{HS}}^2\;\le\;B\cdot\operatorname{mass}(f)\cdot\sum_{i=1}^{b}\Sigma_{H_i}\bigl((\dim V)^{1/b}\bigr).
--   $$
--
--   The subgroups $H_i$ are not required to generate $G$. The theorem converts coset caps for commuting subgroups into a bound by sums of squared degrees of the small irreducible representations of the factors. When the $H_i$ are the permutation groups of the blocks of a partition, the factors are symmetric groups, and the small-degree sums can then be estimated through lower bounds on degrees of irreducible representations of symmetric groups.
--
--   **Formalization Note** $\Sigma_H(R)$ is `smallDegreeSum H R`; irreducible representations of $H$ are indexed by `IrreducibleIndex H`, the isotypic components of the regular representation of $H$ on $\ell^2(H)$, and the degree of an index is the dimension of a chosen simple subspace of that component. The cap is `LeftCosetCap f (H i) B`, with the natural-number index `(H i).index` cast to a real number. $\|\cdot\|_{\mathrm{HS}}^2$ is `hsNormSq`, $\hat f(\rho)$ is `complexFourier ρ (fun g => f g)`, and $\operatorname{mass}(f)$ is `mass f`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/DegreeTransfer.lean#L51-L74

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
variable {G V : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) {b : ℕ} (H : Fin b → Subgroup G)

theorem OAI.PartialPermutation.small_degree_sum_transfer [Representation.IsIrreducible ρ]
    (hb : 0 < b) (hρ : IsUnitary ρ)
    (hcomm : ∀ i j, i ≠ j → ∀ g ∈ H i, ∀ k ∈ H j, Commute g k)
    (f : G → ℝ) (B : ℝ) (hf : ∀ g, 0 ≤ f g) (hcap : ∀ i, LeftCosetCap f (H i) B) :
    (Module.finrank ℂ V : ℝ) * hsNormSq (complexFourier ρ (fun g => f g)) ≤
      B * mass f * ∑ i, smallDegreeSum (H i) ((Module.finrank ℂ V : ℝ)^(1 / (b : ℝ))) := by sorry
