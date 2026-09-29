-- Prove2me | Theorems.Thm_IharaLemma_finite_cornerSubmodule
-- name    : IharaLemma.finite_cornerSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/836b1d7a-4444-51d6-a454-dfb24c6c824a
-- title:
--   Finiteness of the corner submodule eV over the base ring
-- statement:
--   Let $\mathcal{O}$ and $B$ be commutative rings with $B$ an $\mathcal{O}$-algebra, and let $V$ be an abelian group carrying compatible $B$- and $\mathcal{O}$-module structures, the compatibility being that the $\mathcal{O}$-action factors through $B$ via the algebra map (a scalar tower). Let $e$ be an arbitrary element of $B$, and assume $V$ is a finite (i.e. finitely generated) $\mathcal{O}$-module. The conclusion is that the underlying $\mathcal{O}$-module of [`IharaLemma.cornerSubmodule e`](def/IharaLemma_IdempotentSplitting.html#L46), which by definition is the $B$-submodule of $V$ given by the range of the $B$-linear endomorphism $e \cdot \mathrm{id}_V$, that is the image $eV = \{e \cdot v : v \in V\}$, is again a finite $\mathcal{O}$-module. No idempotency, and indeed no hypothesis whatsoever, is imposed on $e$; no Noetherian or flatness assumption on $\mathcal{O}$, $B$ or $V$ is needed either.
--
--   This is the elementary finiteness statement underlying the use of idempotent 'corners' $eV$ of a module over a Hecke-type algebra: cutting out a corner does not destroy finiteness over the coefficient ring. It is used in the cohomological-carrier bookkeeping for Ihara's lemma, being cited by [`CohCarrier.HeckeData.finite_ML_and_free_ML`](thm.html#CohCarrier.HeckeData.finite_ML_and_free_ML) and by [`CohCarrier.exists_sigmaCorner_gammaZero_of_sigmaCorner_gammaH`](thm.html#CohCarrier.exists_sigmaCorner_gammaZero_of_sigmaCorner_gammaH).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IharaLemma_finite_cornerSubmodule.lean

import Definitions.Def_IharaLemma_IdempotentSplitting
import Mathlib.RingTheory.Finiteness.Cardinality

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IharaLemma.finite_cornerSubmodule {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B]
    [Algebra 𝒪 B] {V : Type} [AddCommGroup V] [Module B V] [Module 𝒪 V] [IsScalarTower 𝒪 B V]
    (e : B) [Module.Finite 𝒪 V] :
    Module.Finite 𝒪 ↥(IharaLemma.cornerSubmodule (M := V) e) := by sorry
