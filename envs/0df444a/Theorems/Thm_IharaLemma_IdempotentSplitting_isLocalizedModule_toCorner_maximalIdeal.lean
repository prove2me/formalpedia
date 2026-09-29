-- Prove2me | Theorems.Thm_IharaLemma_IdempotentSplitting_isLocalizedModule_toCorner_maximalIdeal
-- name    : IharaLemma.IdempotentSplitting.isLocalizedModule_toCorner_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/ab0f67ed-6972-5f50-b92e-ee8423bf22ce
-- title:
--   Corner maps of an idempotent splitting are localizations
-- statement:
--   Let $B$ be a commutative ring and let $S$ be an idempotent splitting of $B$, that is: a natural number $S.n$, elements $S.e : \mathrm{Fin}\,S.n \to B$ forming a complete orthogonal family of idempotents, ideals $S.\mathfrak{m} : \mathrm{Fin}\,S.n \to \mathrm{Ideal}\,B$ each of which is maximal, together with the requirements that every maximal ideal of $B$ equals $S.\mathfrak{m}\,i$ for some $i$, and that $S.e\,i \in S.\mathfrak{m}\,j$ holds precisely when $i \neq j$. Fix an index $i$ and let $M$ be any $B$-module. The corner submodule attached to $S.e\,i$ is the range of the endomorphism $S.e\,i \cdot \mathrm{id}$ of $M$, i.e. $(S.e\,i)\cdot M$, and [`IharaLemma.toCorner (S.e i)`](def/IharaLemma_IdempotentSplitting.html#L48) is the $B$-linear map $M \to (S.e\,i)\cdot M$, $v \mapsto S.e\,i \cdot v$, obtained by restricting that endomorphism to its range. The assertion is that this map exhibits $(S.e\,i)\cdot M$ as the localization of $M$ at the multiplicative set $B \setminus S.\mathfrak{m}\,i$: every $s \notin S.\mathfrak{m}\,i$ acts invertibly on the corner, every element of the corner has the form $s^{-1}(S.e\,i \cdot v)$, and $S.e\,i \cdot v = 0$ exactly when $sv = 0$ for some $s \notin S.\mathfrak{m}\,i$.
--
--   This is the module-theoretic form of the standard decomposition of a semilocal ring with finitely many maximal ideals into its local factors: the corner cut out by the idempotent matching a maximal ideal computes the localization there, uniformly in the module. It is used in the construction and analysis of Hecke-module carriers, for instance in establishing finiteness and freeness of localized cohomology modules and in reductions to a single corner.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IharaLemma_IdempotentSplitting_isLocalizedModule_toCorner_maximalIdeal.lean

import Definitions.Def_IharaLemma_IdempotentSplitting
import Mathlib.Algebra.Module.LocalizedModule.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IharaLemma.IdempotentSplitting.isLocalizedModule_toCorner_maximalIdeal {B : Type}
    [CommRing B] (S : IharaLemma.IdempotentSplitting B) (i : Fin S.n) {M : Type}
    [AddCommGroup M] [Module B M] :
    IsLocalizedModule (S.𝔪 i).primeCompl (IharaLemma.toCorner (M := M) (S.e i)) := by sorry
