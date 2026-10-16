-- Prove2me | Theorems.Thm_OAI_PartialPermutation_character_kernel_identity
-- name    : OAI.PartialPermutation.character_kernel_identity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:20:23.479091+00:00
-- url     : https://prove2.me/theorems/893df9bd-b744-4019-b714-94a91f98a515
-- title:
--   The conjugate character kernel acts as the identity in its irreducible representation
-- statement:
--   Let $G$ be a finite group and $V$ a finite-dimensional complex inner product space (inner product conjugate-linear in the first argument). Let $\rho$ be an irreducible representation of $G$ on $V$ which is unitary, $\langle\rho(g)x,\rho(g)y\rangle=\langle x,y\rangle$ for all $g\in G$ and $x,y\in V$. Write $d=\dim_{\mathbb C}V$, $\chi(g)=\operatorname{tr}\rho(g)$ for the character of $\rho$, and for a function $a\colon G\to\mathbb{C}$ write $\hat a(\rho)=\sum_{g\in G}a(g)\,\rho(g)\in\operatorname{End}(V)$ for its Fourier transform at $\rho$. Then the kernel $k(g)=\frac{d}{|G|}\,\overline{\chi(g)}$ satisfies
--   $$
--   \hat k(\rho)=\sum_{g\in G}\frac{d}{|G|}\,\overline{\chi(g)}\,\rho(g)=I_V .
--   $$
--
--   Because $\rho$ is unitary, $\overline{\chi(g)}=\chi(g^{-1})$, so $k$ is the coefficient function of the central idempotent $\frac{d}{|G|}\sum_g\chi(g^{-1})\,g$ of the group algebra attached to $\rho$, and the identity says that this idempotent acts as the identity on $V$. It provides an explicit function whose Fourier transform at $\rho$ is the identity operator.
--
--   **Formalization Note** The Fourier transform is `complexFourier ρ`, the character is Mathlib's `Representation.character`, unitarity is the hypothesis `IsUnitary ρ` and irreducibility is the instance `Representation.IsIrreducible ρ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/Characters.lean#L52-L76

import Mathlib
import Definitions.Def_PartialPermutation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SchurAverage

open OAI OAI.PartialPermutation
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate MonoidAlgebra
variable {G V : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
include hρ
variable [Representation.IsIrreducible ρ]

theorem OAI.PartialPermutation.character_kernel_identity :
    complexFourier ρ (fun g => ((Module.finrank ℂ V : ℂ) / Fintype.card G) *
      conj (ρ.character g)) = 1 := by sorry
