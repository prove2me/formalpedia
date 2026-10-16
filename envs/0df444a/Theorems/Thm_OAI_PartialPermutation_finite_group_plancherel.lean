-- Prove2me | Theorems.Thm_OAI_PartialPermutation_finite_group_plancherel
-- name    : OAI.PartialPermutation.finite_group_plancherel
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:20:46.129165+00:00
-- url     : https://prove2.me/theorems/4291ea4a-3464-4811-8aa2-04619df8d4b0
-- title:
--   Plancherel formula for the Fourier transform on a finite group
-- statement:
--   Let $G$ be a finite group and let $\ell^2(G)$ be the space of functions $G\to\mathbb{C}$ with inner product $\langle a,b\rangle=\sum_{g}\overline{a(g)}\,b(g)$, on which $G$ acts unitarily by left translation, $(\lambda(g)a)(h)=a(g^{-1}h)$. Regard $\ell^2(G)$ as a module over the group algebra $\mathbb{C}[G]$ and let $\mathrm{Irr}(G)$ be the finite set of its isotypic components. For each $c\in\mathrm{Irr}(G)$ take the chosen simple submodule $W_c\subseteq\ell^2(G)$ lying in $c$, with the inner product inherited from $\ell^2(G)$; let $\rho_c$ be the restriction of $\lambda$ to $W_c$ and $d_c=\dim_{\mathbb C}W_c$. Every irreducible representation of $G$ is equivalent to exactly one $\rho_c$, so $\mathrm{Irr}(G)$ indexes the irreducible representations of $G$. For $a\colon G\to\mathbb{C}$ let $\hat a(\rho_c)=\sum_{g\in G}a(g)\rho_c(g)\in\operatorname{End}(W_c)$, and for an operator $A$ let $\|A\|_{\mathrm{HS}}^2=\operatorname{Re}\operatorname{tr}(A^*A)$ be its squared Hilbert–Schmidt norm.
--
--   Then for every $a\colon G\to\mathbb{C}$,
--   $$
--   |G|\sum_{g\in G}|a(g)|^2=\sum_{c\in\mathrm{Irr}(G)}d_c\,\bigl\|\hat a(\rho_c)\bigr\|_{\mathrm{HS}}^2 .
--   $$
--
--   This is the Plancherel (Parseval) identity of non-abelian Fourier analysis on a finite group: up to the weights $d_c/|G|$, the Fourier transform $a\mapsto(\hat a(\rho_c))_c$ is an isometry from $\ell^2(G)$ into $\bigoplus_c\operatorname{End}(W_c)$ with Hilbert–Schmidt norms. It converts $\ell^2$ information about a function into Hilbert–Schmidt information about its Fourier coefficients, and is used, for example, to compute the $\ell^2$ mass of kernels that are defined through their Fourier transforms.
--
--   **Formalization Note** `IrreducibleIndex G` is the type of isotypic components of `(regularRep G).asModule`, `irreducibleSpace c` is the chosen simple submodule `componentSimple` viewed as a subspace of `EuclideanSpace ℂ G`, `irreducibleRep c` is the restricted representation and `irreducibleDegree c` its dimension. `hsNormSq A` is defined as the real part of `trace (adjoint A * A)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/Plancherel.lean#L111-L145

import Mathlib
import Definitions.Def_PartialPermutation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SchurAverage
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ModuleTransport
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Components
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CentralKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CompleteKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RegularRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Plancherel

open OAI OAI.PartialPermutation
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical
open scoped BigOperators MonoidAlgebra Classical
variable {G : Type*} [Group G] [Fintype G]

theorem OAI.PartialPermutation.finite_group_plancherel (a : G → ℂ) :
    (Fintype.card G : ℝ) * ∑ g, ‖a g‖^2 =
      ∑ c : IrreducibleIndex G, (irreducibleDegree c : ℝ) *
        hsNormSq (V := irreducibleSpace c) (complexFourier (V := irreducibleSpace c) (irreducibleRep c) a) := by sorry
