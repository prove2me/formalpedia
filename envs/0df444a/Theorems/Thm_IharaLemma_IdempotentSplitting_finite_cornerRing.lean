-- Prove2me | Theorems.Thm_IharaLemma_IdempotentSplitting_finite_cornerRing
-- name    : IharaLemma.IdempotentSplitting.finite_cornerRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/f86cdd0f-1e21-5ece-b8d1-793c3ebac96c
-- title:
--   Corner rings of an idempotent splitting are module-finite
-- statement:
--   Let $\mathcal{O}$ be a commutative ring and $B$ a commutative $\mathcal{O}$-algebra. Let $S$ be an [`IharaLemma.IdempotentSplitting`](def/IharaLemma_IdempotentSplitting.html#L7) of $B$, that is: a natural number $n$, a family $e : \mathrm{Fin}\,n \to B$, and a family $\mathfrak{m} : \mathrm{Fin}\,n \to$ (ideals of $B$) such that the $e_i$ form a complete orthogonal family of idempotents (pairwise orthogonal idempotents summing to $1$), each $\mathfrak{m}_i$ is a maximal ideal, every maximal ideal of $B$ occurs as some $\mathfrak{m}_i$, and $e_i \in \mathfrak{m}_j$ if and only if $i \neq j$. Fix an index $i$, and assume that $B$ is a finite $\mathcal{O}$-module. The conclusion is that the corner ring $S.\mathrm{CornerRing}\ i$ — the corner of $B$ at the idempotent $e_i$ in the sense of Mathlib, i.e. the ring $e_i B e_i = e_i B$ with unit $e_i$ — is again a finite $\mathcal{O}$-module.
--
--   This is the finiteness bookkeeping attached to the idempotent decomposition of a semilocal ring $B$ into its local corners: the summands inherit module-finiteness over the base ring. It is used where Hecke algebras and their Galois lattices are cut into corners, namely in the construction of a corner-scalar identity for the Hecke operator at the residue characteristic on $\Gamma_0$-level cusp forms and in the production of a basis adapted to a corner submodule from an involution and a similitude pairing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IharaLemma_IdempotentSplitting_finite_cornerRing.lean

import Definitions.Def_IharaLemma_IdempotentSplitting
import Mathlib.RingTheory.Finiteness.Cardinality

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IharaLemma.IdempotentSplitting.finite_cornerRing {𝒪 : Type} [CommRing 𝒪] {B : Type}
    [CommRing B] [Algebra 𝒪 B] (S : IharaLemma.IdempotentSplitting B) (i : Fin S.n)
    [Module.Finite 𝒪 B] : Module.Finite 𝒪 (S.CornerRing i) := by sorry
