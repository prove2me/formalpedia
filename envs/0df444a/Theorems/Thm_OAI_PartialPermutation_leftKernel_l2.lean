-- Prove2me | Theorems.Thm_OAI_PartialPermutation_leftKernel_l2
-- name    : OAI.PartialPermutation.leftKernel_l2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:23:35.131967+00:00
-- url     : https://prove2.me/theorems/a397460f-1df7-42ac-a98d-1bde47fe2efb
-- title:
--   $\ell^2$ bound for convolution with a subgroup kernel under a right coset cap
-- statement:
--   Let $G$ be a finite group, $H\le G$ a subgroup of index $[G:H]$, $k\colon H\to\mathbb{C}$ any function, $f\colon G\to\mathbb{R}$ a function with $f(g)\ge0$ for all $g$, and $B\in\mathbb{R}$. Write $\mathrm{mass}(f)=\sum_{g\in G}f(g)$ and define the convolution of $k$ (extended by zero outside $H$) with $f$,
--   $$
--   L(g)=\sum_{h\in H}k(h)\,f(h^{-1}g)\qquad(g\in G).
--   $$
--   Assume the right coset cap: every right coset $Hg$ carries $f$-mass at most $B/[G:H]$, that is, $\sum_{h\in H}f(hg)\le B/[G:H]$ for every $g\in G$. Then
--   $$
--   \sum_{g\in G}|L(g)|^2\le\frac{B}{[G:H]}\,\mathrm{mass}(f)\sum_{h\in H}|k(h)|^2 .
--   $$
--
--   For a representation $\rho$ of $G$, the Fourier transform of $L$ factors as $\hat L(\rho)=\hat k(\rho|_H)\,\hat f(\rho)$, where $\hat a(\sigma)=\sum_xa(x)\sigma(x)$. Combined with the Fourier–Bessel inequality, this $\ell^2$ estimate therefore bounds Hilbert–Schmidt norms of products of a subgroup Fourier transform with the Fourier transform of a density that is spread out over the cosets of $H$.
--
--   **Formalization Note** `leftKernel H k f` is $L$, `mass f` is $\mathrm{mass}(f)$ and `RightCosetCap f H B` is the cap hypothesis; the index `H.index` is a natural number cast to the reals, positive because $G$ is finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/ConvolutionKernels.lean#L31-L57

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

open OAI OAI.PartialPermutation
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical
attribute [local instance] Classical.propDecidable
open scoped BigOperators ComplexConjugate
variable {G : Type*} [Group G] [Fintype G]

theorem OAI.PartialPermutation.leftKernel_l2 (H : Subgroup G) (k : H → ℂ) (f : G → ℝ) (B : ℝ)
    (hf : ∀ g, 0 ≤ f g) (hcap : RightCosetCap f H B) :
    ∑ g, ‖leftKernel H k f g‖ ^ 2 ≤
      B / H.index * mass f * ∑ h : H, ‖k h‖ ^ 2 := by sorry
