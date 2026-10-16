-- Prove2me | Theorems.Thm_OAI_PartialPermutation_complexFourier_smallTypeKernel
-- name    : OAI.PartialPermutation.complexFourier_smallTypeKernel
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:27:06.905093+00:00
-- url     : https://prove2.me/theorems/d19b701a-539c-4439-a674-e5cd2464c518
-- title:
--   The small-type kernel acts as the identity or as zero on each irreducible representation
-- statement:
--   Let $G$ be a finite group. Let $\mathrm{Irr}(G)$ be the finite set of isotypic components of the left regular representation of $G$ on $\ell^2(G)$; for $c\in\mathrm{Irr}(G)$ let $\rho_c$ be the chosen irreducible subrepresentation in $c$, $d_c$ its dimension and $\chi_c$ its character. Every irreducible representation of $G$ is equivalent to exactly one $\rho_c$. For $R\in\mathbb{R}$ define the small-type kernel
--   $$
--   K_R(g)=\sum_{c\in\mathrm{Irr}(G):\ d_c\le R}\frac{d_c}{|G|}\,\chi_c(g^{-1})\qquad(g\in G).
--   $$
--   Let $V$ be a finite-dimensional complex vector space and $\rho$ an irreducible representation of $G$ on $V$, and write $\hat a(\rho)=\sum_{g}a(g)\rho(g)$ for the Fourier transform of $a\colon G\to\mathbb{C}$. Then
--   $$
--   \widehat{K_R}(\rho)=\begin{cases}I_V,&\dim_{\mathbb C}V\le R,\\0,&\dim_{\mathbb C}V>R.\end{cases}
--   $$
--
--   Thus $K_R$ acts as the identity on every irreducible representation of dimension at most $R$ and as zero on all others; in this sense it is the convolution kernel of the projection onto the low-dimensional irreducible types. This is used to cut a representation down to its low-dimensional constituents, with complete control of the kernel on the Fourier side.
--
--   **Formalization Note** `smallTypeKernel G R` is $K_R$, built from `centralCharacterKernel (irreducibleRep c) g`, which equals $\frac{d_c}{|G|}\chi_c(g^{-1})$; the conditions compare natural-number dimensions with $R$ after casting to the reals. No inner product on $V$ is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/SmallKernels.lean#L29-L59

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

open OAI OAI.PartialPermutation
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical
attribute [local instance] Classical.propDecidable
variable {G : Type*} [Group G] [Fintype G]

theorem OAI.PartialPermutation.complexFourier_smallTypeKernel {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (R : ℝ) : complexFourier ρ (smallTypeKernel G R) =
      if (Module.finrank ℂ V : ℝ) ≤ R then 1 else 0 := by sorry
