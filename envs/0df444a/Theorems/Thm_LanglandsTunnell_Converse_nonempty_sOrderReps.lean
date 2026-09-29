-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_nonempty_sOrderReps
-- name    : LanglandsTunnell.Converse.nonempty_sOrderReps
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/66545069-114b-5520-93bd-251c496473a2
-- title:
--   Existence of representatives for order vectors at finitely many places
-- statement:
--   Let $K$ be a number field and let $S$ be a finite set of height-one primes of its ring of integers $\mathcal{O}_K$, i.e. of finite places of $K$. The assertion is that the type `SOrderReps K S` is nonempty, that is, there exists a family of elements of $K^\times$ indexed by the integer vectors $n \in \mathbb{Z}^{S}$: a map $n \mapsto \mathrm{rep}(n) \in K^\times$ such that for every $n \colon S \to \mathbb{Z}$ and every $v \in S$ the image of $\mathrm{rep}(n)$ under the canonical map $K^\times \to (K_v)^\times$ — the unit group of the $v$-adic completion $K_v$, the image being `localOf K v (rep n)` — has valuation $\mathrm{WithZero.exp}(-n_v)$ for the canonical valuation on $K_v$. With the normalisation in which a uniformiser has valuation $\mathrm{exp}(-1)$, this says $\operatorname{ord}_v(\mathrm{rep}(n)) = n_v$ for all $v \in S$ simultaneously. The statement is an existence (nonemptiness) assertion about the whole family, uniformly in $n$; no compatibility between the elements $\mathrm{rep}(n)$ for different $n$, and no condition at places outside $S$, is required.
--
--   Such a family is a system of representatives for the vectors of orders at the finitely many exceptional finite places, of the kind indexing the local data in the converse theorem of Jacquet–Langlands; it is used downstream by [`LanglandsTunnell.Converse.exists_isJLNice_of_forall_isNicePinned`](thm.html#LanglandsTunnell.Converse.exists_isJLNice_of_forall_isNicePinned).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_nonempty_sOrderReps.lean

import Definitions.Def_LanglandsTunnell_JLData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IsDedekindDomain NumberField

theorem LanglandsTunnell.Converse.nonempty_sOrderReps (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) : Nonempty (SOrderReps K S) := by sorry
