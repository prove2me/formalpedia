-- Prove2me | Theorems.Thm_OAI_PartialPermutation_small_type_hs_bound
-- name    : OAI.PartialPermutation.small_type_hs_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:28:46.691236+00:00
-- url     : https://prove2.me/theorems/687874b2-8beb-4d93-b004-468e39f8a763
-- title:
--   Hilbert–Schmidt bound for a coset-capped Fourier transform composed with a subgroup small-type kernel
-- statement:
--   Let $G$ be a finite group, $V$ a finite-dimensional complex inner product space of dimension $D$, and $\rho$ an irreducible unitary representation of $G$ on $V$. Let $H\le G$ be a subgroup of index $[G:H]$ and $\rho|_H$ the restriction of $\rho$ to $H$. For a finite group $\Gamma$, a representation $\sigma$ of $\Gamma$ and $a\colon\Gamma\to\mathbb{C}$ write $\hat a(\sigma)=\sum_{x\in\Gamma}a(x)\sigma(x)$, and write $\|A\|_{\mathrm{HS}}^2=\operatorname{Re}\operatorname{tr}(A^*A)$ for the squared Hilbert–Schmidt norm.
--
--   Let $\mathrm{Irr}(H)$ be the set of isotypic components of the left regular representation of $H$ on $\ell^2(H)$, with chosen irreducible representatives $\rho_c$ of dimension $d_c$ and character $\chi_c$. For $R\in\mathbb{R}$ define the small-type kernel of $H$ and the small-degree sum
--   $$
--   K^H_R(h)=\sum_{c\in\mathrm{Irr}(H):\ d_c\le R}\frac{d_c}{|H|}\,\chi_c(h^{-1}),\qquad S_H(R)=\sum_{c\in\mathrm{Irr}(H):\ d_c\le R}d_c^2 .
--   $$
--
--   Let $f\colon G\to\mathbb{R}$ be nonnegative with $\mathrm{mass}(f)=\sum_gf(g)$, and let $B\in\mathbb{R}$ be such that $f$ satisfies the left coset cap $\sum_{h\in H}f(gh)\le B/[G:H]$ for every $g\in G$. Then
--   $$
--   D\,\Bigl\|\hat f(\rho)\,\widehat{K^H_R}(\rho|_H)\Bigr\|_{\mathrm{HS}}^2\le B\,\mathrm{mass}(f)\,S_H(R).
--   $$
--
--   The operator $\widehat{K^H_R}(\rho|_H)$ acts as the identity on each irreducible $H$-subrepresentation of $V$ of dimension at most $R$ and as zero on the others. The inequality therefore says that a density spread evenly over the left cosets $gH$ has small Fourier transform on the part of $V$ where $H$ acts through low-dimensional irreducibles, with a bound governed by the total size $S_H(R)$ of those irreducibles.
--
--   **Formalization Note** The left coset cap is `LeftCosetCap f H B`, $K^H_R$ is `smallTypeKernel H R` (built from the irreducible representations of the group $H$ itself), $S_H(R)$ is `smallDegreeSum H R`, and $\rho|_H$ is `ρ.comp H.subtype`. The real function $f$ enters the Fourier transform through its coercion to complex values.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/ProjectionCovers.lean#L49-L67

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

theorem OAI.PartialPermutation.small_type_hs_bound {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    [Representation.IsIrreducible ρ] (H : Subgroup G) (R : ℝ)
    (f : G → ℝ) (B : ℝ) (hf : ∀ g, 0 ≤ f g) (hcap : LeftCosetCap f H B) :
    (Module.finrank ℂ V : ℝ) *
      hsNormSq (complexFourier ρ (fun g => f g) *
        complexFourier (ρ.comp H.subtype) (smallTypeKernel H R)) ≤
      B * mass f * smallDegreeSum H R := by sorry
