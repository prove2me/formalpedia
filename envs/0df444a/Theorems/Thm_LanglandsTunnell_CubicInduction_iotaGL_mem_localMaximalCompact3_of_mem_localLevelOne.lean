-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_iotaGL_mem_localMaximalCompact3_of_mem_localLevelOne
-- name    : LanglandsTunnell.CubicInduction.iotaGL_mem_localMaximalCompact3_of_mem_localLevelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/29c001c0-31c6-596d-bdde-2d3b3fd31644
-- title:
--   Level-one g at v gives diag(g,1) integral in GL₃
-- statement:
--   Let $v$ be a point of the height-one spectrum of the ring of integers $\mathcal{O}_{\mathbb{Q}}$ of $\mathbb{Q}$, and let $g$ be an element of $GL_2$ over the $v$-adic completion $K_v$ of $\mathbb{Q}$. Assume $g$ lies in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), that is, in the preimage under the monoid homomorphism [`AdelicDock.localEmbed`](def/AdelicDock_LocalEmbedding.html#L97) — which sends $g$ to the invertible matrix `localMat` over the finite adèle ring of $\mathbb{Q}$ built from $g$ at the place $v$ — of the subgroup `AdelicLevel.finiteLevelOne` at the unit ideal $N = \top$, whose elements are the invertible $2\times 2$ matrices over the finite adèle ring such that both the matrix itself and the matrix of its inverse satisfy the predicate `IsLevelOneMatrix (𝓞 ℚ) ℚ ⊤`; at the unit ideal this level-one condition in particular makes all entries integral. The conclusion is that `iotaGL g`, the element of $GL_3(K_v)$ whose matrix is $\mathrm{diag}(g,1)$, i.e. $g$ in the upper-left $2\times 2$ block, entry $1$ in position $(2,2)$ and zeros in the remaining places of the last row and column, belongs to `localMaximalCompact3 (𝓞 ℚ) ℚ v`: every entry of this $3\times3$ matrix and every entry of the matrix of its inverse has $v$-adic valuation at most $1$.
--
--   This is the compatibility of the embedding $g \mapsto \mathrm{diag}(g,1)$ of $GL_2$ into $GL_3$ with the integral structures at a finite place: a local level-one matrix at the unit ideal lands in the maximal compact subgroup of $GL_3(K_v)$. It is used in the cubic-induction part of the Langlands–Tunnell argument, by the statements on normalised new vectors for local Whittaker data and on spherical torus values of induced coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_iotaGL_mem_localMaximalCompact3_of_mem_localLevelOne.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.iotaGL_mem_localMaximalCompact3_of_mem_localLevelOne
    (v : HeightOneSpectrum (𝓞 ℚ)) {g : GL (Fin 2) (v.adicCompletion ℚ)}
    (hg : g ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) :
    iotaGL g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v := by sorry
