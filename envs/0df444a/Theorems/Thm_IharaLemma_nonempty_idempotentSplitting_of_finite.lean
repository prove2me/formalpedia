-- Prove2me | Theorems.Thm_IharaLemma_nonempty_idempotentSplitting_of_finite
-- name    : IharaLemma.nonempty_idempotentSplitting_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/aab5202a-688e-52a2-bd09-09081040ffc3
-- title:
--   Idempotent splitting of a finite algebra over a complete local ring
-- statement:
--   Let $\mathcal{O}$ be a commutative local noetherian ring which is complete for the adic topology of its maximal ideal (in the sense of `IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪`, i.e. Hausdorff and precomplete for that ideal), and let $B$ be a commutative $\mathcal{O}$-algebra which is finite as an $\mathcal{O}$-module. The assertion is that the type [`IharaLemma.IdempotentSplitting B`](def/IharaLemma_IdempotentSplitting.html#L7) is nonempty, that is: there exist a natural number $n$, elements $e_0,\dots,e_{n-1}$ of $B$ and ideals $\mathfrak{m}_0,\dots,\mathfrak{m}_{n-1}$ of $B$, indexed by `Fin n`, such that the $e_i$ form a complete orthogonal family of idempotents of $B$ (Mathlib's `CompleteOrthogonalIdempotents`), each $\mathfrak{m}_i$ is a maximal ideal, every maximal ideal of $B$ occurs among the $\mathfrak{m}_i$, and $e_i \in \mathfrak{m}_j$ holds precisely when $i \neq j$. The last condition in particular forces the indexing $i \mapsto \mathfrak{m}_i$ to be injective, so the $\mathfrak{m}_i$ enumerate the maximal ideals of $B$ without repetition, and $B$ is correspondingly a product of $n$ local rings $e_i B$; the statement records the idempotents and the enumeration rather than the product decomposition itself.
--
--   This is the standard decomposition of a module-finite algebra over a complete local noetherian ring into a finite product of local rings, obtained by lifting the idempotents of the semilocal quotient; here it is packaged as the existence of a complete orthogonal family of idempotents matched with an enumeration of the maximal ideals. It supplies the local factors used when localising Hecke algebras and their cohomology modules at maximal ideals in the work towards Ihara's lemma.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IharaLemma_nonempty_idempotentSplitting_of_finite.lean

import Definitions.Def_IharaLemma_IdempotentSplitting
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Noetherian.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IharaLemma.nonempty_idempotentSplitting_of_finite (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    [IsNoetherianRing 𝒪] (B : Type) [CommRing B] [Algebra 𝒪 B] [Module.Finite 𝒪 B]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] :
    Nonempty (IharaLemma.IdempotentSplitting B) := by sorry
