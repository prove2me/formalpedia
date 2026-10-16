-- Prove2me | Theorems.Thm_OAI_PartialPermutation_smallTypeKernel_identity_of_kernel
-- name    : OAI.PartialPermutation.smallTypeKernel_identity_of_kernel
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:28:17.096034+00:00
-- url     : https://prove2.me/theorems/3fa39c70-9244-4946-8ef7-ba98145863bf
-- title:
--   An identity-acting kernel of small $\ell^2$ mass forces the small-type kernel to act as the identity
-- statement:
--   Let $G$ be a finite group and $V$ a finite-dimensional complex inner product space carrying a unitary representation $\rho$ of $G$, i.e. $\langle\rho(g)x,\rho(g)y\rangle=\langle x,y\rangle$ for all $g\in G$ and $x,y\in V$; $\rho$ need not be irreducible. For $a\colon G\to\mathbb{C}$ write $\hat a(\rho)=\sum_{g}a(g)\rho(g)$. Let $\mathrm{Irr}(G)$ be the set of isotypic components of the left regular representation of $G$ on $\ell^2(G)$, with chosen irreducible representatives $\rho_c$ of dimension $d_c$ and character $\chi_c$, and for $R\in\mathbb{R}$ let $K_R(g)=\sum_{c:\ d_c\le R}\frac{d_c}{|G|}\chi_c(g^{-1})$ be the small-type kernel.
--
--   Let $k\colon G\to\mathbb{C}$, $d\in\mathbb{N}$ and $R\in\mathbb{R}$ satisfy
--   $$
--   d\le R,\qquad\sum_{g\in G}|k(g)|^2=\frac{d^2}{|G|},\qquad\hat k(\rho)=I_V .
--   $$
--   Then
--   $$
--   \widehat{K_R}(\rho)=I_V .
--   $$
--
--   The hypotheses say that some kernel of $\ell^2$ mass $d^2/|G|$ acts as the identity on $V$. The conclusion replaces this ad hoc kernel by the canonical kernel $K_R$, whose action on every irreducible representation is known exactly (the identity in dimension at most $R$, zero otherwise).
--
--   **Formalization Note** Unitarity is the hypothesis `IsUnitary ρ`, $d$ is a natural number cast to the reals, and `smallTypeKernel G R` is $K_R$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/SmallKernels.lean#L77-L94

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

theorem OAI.PartialPermutation.smallTypeKernel_identity_of_kernel {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    (k : G → ℂ) (d : ℕ) (R : ℝ) (hd : (d : ℝ) ≤ R)
    (hk : ∑ g, ‖k g‖^2 = (d : ℝ)^2 / Fintype.card G)
    (hact : complexFourier ρ k = 1) : complexFourier ρ (smallTypeKernel G R) = 1 := by sorry
