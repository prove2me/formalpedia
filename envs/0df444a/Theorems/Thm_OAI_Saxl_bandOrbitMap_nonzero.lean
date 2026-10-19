-- Prove2me | Theorems.Thm_OAI_Saxl_bandOrbitMap_nonzero
-- name    : OAI.Saxl.bandOrbitMap_nonzero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:18:03.218473+00:00
-- url     : https://prove2.me/theorems/fd51211a-8288-4520-a13c-5836ae0c8c29
-- title:
--   The colored band orbit map of a nonzero stabilizer-invariant map is nonzero
-- statement:
--   Let $n,a,b,k\in\mathbb{N}$. Write $[m]=\{0,1,\dots,m-1\}$ and let $S_m$ be the symmetric group on $[m]$. Let $e:[n]\to[a]\sqcup[b]$ be a bijection; it splits the $n$ positions into $a$ *left* positions $e^{-1}([a])$ and $b$ *right* positions $e^{-1}([b])$. For $h\in S_a$ and $q\in S_b$ let $h\oplus q=e^{-1}\circ(h\sqcup q)\circ e\in S_n$ be the permutation that acts as $h$ on the left positions and as $q$ on the right positions.
--
--   Let $X$ and $Y$ be complex vector spaces (of any dimension), let $\rho$ be a representation of $S_n$ on $X$, let $c:[b]\to[k]$ be a coloring of the right positions with $k$ colors, and let $F:X\to Y$ be a linear map. The *band orbit map* $\Phi=\Phi_{e,\rho,c,F}$ is the linear map from $X$ to the space of $Y$-valued functions on colorings $w:[b]\to[k]$ given by
--   $$
--   \Phi(x)(w)=\sum_{g\in S_b}\bigl[\,c\circ g^{-1}=w\,\bigr]\;F\bigl(\rho(1\oplus g^{-1})\,x\bigr),
--   $$
--   where the bracket is $1$ if the condition holds and $0$ otherwise.
--
--   Suppose that $F\neq0$ and that $F$ is invariant under the stabilizer of the coloring $c$, acting on the right positions:
--   $$
--   F\bigl(\rho(1\oplus g)\,x\bigr)=F(x)\qquad\text{for all }g\in S_b\text{ with }c\circ g=c\text{ and all }x\in X.
--   $$
--   Then $\Phi_{e,\rho,c,F}\neq0$.
--
--   The band orbit map spreads a map that is invariant under the Young subgroup $\{g\in S_b:c\circ g=c\}$ over all colorings in the $S_b$-orbit of $c$. Together with its equivariance under $S_a\times S_b$, this nonvanishing statement produces the nonzero colored family of maps that is glued with band intertwiners in the support-transfer argument for horizontal strips.
--
--   **Formalization Note** $\Phi$ is `bandOrbitMap e ρ c F` and $h\oplus q$ is `sumPerm e h q`; colorings are functions `Fin b → Fin k`, and the bracket is the value at $w$ of the basis vector `Pi.single (c ∘ g⁻¹) 1`. No finiteness of $X$ or $Y$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/BandOrbit.lean#L68-L85

import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_ColumnContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandPairing
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandSupport
import Definitions.Def_OAI_RepresentationTheory_Saxl_ShapeRigidity
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtClassification
import Definitions.Def_OAI_RepresentationTheory_Saxl_SupportSeparation
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandOrbit

open OAI OAI.Saxl
open scoped TensorProduct
universe uX uY

theorem OAI.Saxl.bandOrbitMap_nonzero {n a b k : ℕ} {X : Type uX} {Y : Type uY}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (e : Fin n ≃ Fin a ⊕ Fin b) (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (c : Fin b → Fin k) (F : X →ₗ[ℂ] Y) (hF0 : F ≠ 0)
    (hF : ∀ g : Equiv.Perm (Fin b), c ∘ g = c → ∀ x, F (ρ (sumPerm e 1 g) x) = F x) :
    bandOrbitMap e ρ c F ≠ 0 := by sorry
