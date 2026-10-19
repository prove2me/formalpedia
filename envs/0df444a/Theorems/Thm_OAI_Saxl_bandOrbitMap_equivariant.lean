-- Prove2me | Theorems.Thm_OAI_Saxl_bandOrbitMap_equivariant
-- name    : OAI.Saxl.bandOrbitMap_equivariant
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:20:05.958096+00:00
-- url     : https://prove2.me/theorems/95b886ab-2b50-4f25-8d71-f71edf9c35af
-- title:
--   Equivariance of the colored band orbit map under the Young subgroup $S_a\times S_b$
-- statement:
--   Let $n,a,b,k\in\mathbb{N}$. Write $[m]=\{0,1,\dots,m-1\}$ and let $S_m$ be the symmetric group on $[m]$. Let $e:[n]\to[a]\sqcup[b]$ be a bijection; it splits the $n$ positions into $a$ *left* positions $e^{-1}([a])$ and $b$ *right* positions $e^{-1}([b])$. For $h\in S_a$ and $q\in S_b$ let $h\oplus q=e^{-1}\circ(h\sqcup q)\circ e\in S_n$ be the permutation that acts as $h$ on the left positions and as $q$ on the right positions.
--
--   Let $X$ and $Y$ be complex vector spaces (of any dimension), let $\rho$ be a representation of $S_n$ on $X$ and $\tau$ a representation of $S_a$ on $Y$, let $c:[b]\to[k]$ be a coloring and let $F:X\to Y$ be linear. The *band orbit map* $\Phi=\Phi_{e,\rho,c,F}$ sends $x\in X$ to the $Y$-valued function on colorings $w:[b]\to[k]$
--   $$
--   \Phi(x)(w)=\sum_{g\in S_b}\bigl[\,c\circ g^{-1}=w\,\bigr]\;F\bigl(\rho(1\oplus g^{-1})\,x\bigr),
--   $$
--   where the bracket is $1$ if the condition holds and $0$ otherwise.
--
--   Assume that $F$ intertwines the action of the left block, $F(\rho(h\oplus1)x)=\tau(h)F(x)$ for all $h\in S_a$ and $x\in X$. Then for all $h\in S_a$, $q\in S_b$, $x\in X$ and every coloring $w:[b]\to[k]$,
--   $$
--   \Phi\bigl(\rho(h\oplus q)\,x\bigr)(w)=\tau(h)\Bigl(\Phi(x)(w\circ q)\Bigr).
--   $$
--   No condition on the coloring $c$ is needed.
--
--   Equivalently, $\Phi$ is a homomorphism of $S_a\times S_b$-representations from $X$ (with $(h,q)$ acting by $\rho(h\oplus q)$) to the space of $Y$-valued functions on colorings, where $(h,q)$ acts by $\psi\mapsto\bigl(w\mapsto\tau(h)\,\psi(w\circ q)\bigr)$: through $\tau$ on the values and by permuting the positions of the colorings. This is the equivariance input for gluing the band orbit map with band intertwiners.
--
--   **Formalization Note** $\Phi$ is `bandOrbitMap e ρ c F`, $h\oplus q$ is `sumPerm e h q`, and colorings are functions `Fin b → Fin k`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/BandOrbit.lean#L87-L119

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

theorem OAI.Saxl.bandOrbitMap_equivariant {n a b k : ℕ} {X : Type uX} {Y : Type uY}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (e : Fin n ≃ Fin a ⊕ Fin b) (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (τ : Representation ℂ (Equiv.Perm (Fin a)) Y)
    (c : Fin b → Fin k) (F : X →ₗ[ℂ] Y)
    (hF : ∀ h : Equiv.Perm (Fin a), ∀ x, F (ρ (sumPerm e h 1) x) = τ h (F x))
    (h : Equiv.Perm (Fin a)) (q : Equiv.Perm (Fin b)) (x : X) (w : Fin b → Fin k) :
    bandOrbitMap e ρ c F (ρ (sumPerm e h q) x) w =
      τ h (bandOrbitMap e ρ c F x (w ∘ q)) := by sorry
